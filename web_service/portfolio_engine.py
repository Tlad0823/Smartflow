# -*- coding: utf-8 -*-
"""
가계부 연동 자산배분 · 리밸런싱 엔진 (Portfolio Guardrail Engine)

STAGE 1  재무 체력 측정 & 필수 비상금(C_reserve) 산출
STAGE 2  온보딩 설문 & 2단계 가드레일 위험 성향(Tier 1~5) 산출
STAGE 3  7대 표준 자산군 매핑 / 시가 평가 / 비중 이탈도(Gap)
         경로 A: 신규 투자자 빌드업(3회 분할 매수, 구축 중 트리거 대응)
         경로 B: 기존 보유자 전환 (전략 A 즉시 리밸런싱 / 전략 B 점진적 리밸런싱)
         전환 완료 3중 검증 + 180일 Time-out
STAGE 4  가계부 연동 정식 관리 모드
         Trigger A(비상금 침범) / B(재무 잉여율 위기) / C(단기 목돈 지출)
         스마트 바이 → 밴드(±5%p) 리밸런싱 → 5대 실행 가드레일 → 1-Click 승인 발주
         연 1회 정기 재평가

단위 규칙: 비중·Gap·수익률·변동성·Buffer는 모두 % 단위(예: 12.5 = 12.5%), 금액은 원.
실제 증권사/마이데이터 연동부는 BrokerAPI 등 인터페이스로만 두었습니다.
"""
from __future__ import annotations

import copy
import hashlib
import hmac
import math
import os
import re
from dataclasses import dataclass, field
from datetime import date, datetime, time as dtime, timedelta
from enum import Enum
from typing import Callable, Optional

# ── 시계: 엔진이 쓰는 '오늘'을 한 곳에서 주입 ─────────────────────────────────
# 실행 중에는 시스템 시계, 테스트·백테스트에서는 FixedClock 으로 원하는 날짜를 넣습니다.
#   with frozen_clock(date(2020, 3, 2)): ...     # 그 날짜인 것처럼 실행
class Clock:
    def now(self) -> datetime:
        raise NotImplementedError

    def today(self) -> date:
        return self.now().date()


class SystemClock(Clock):
    def now(self) -> datetime:
        return datetime.now()


class FixedClock(Clock):
    """고정 시계 (advance 로 시간을 앞으로 돌릴 수 있음)"""

    def __init__(self, at):
        self.at = at if isinstance(at, datetime) else datetime.combine(at, dtime(7, 0))

    def now(self) -> datetime:
        return self.at

    def advance(self, days: int = 0, hours: int = 0) -> None:
        self.at += timedelta(days=days, hours=hours)

    def set(self, at) -> None:
        self.at = at if isinstance(at, datetime) else datetime.combine(at, self.at.time())


class OffsetClock(Clock):
    """시스템 시계를 특정 날짜로 옮긴 시계 — 시간은 실제처럼 흐름 (모의 날짜로 서버 실행)"""

    def __init__(self, start):
        start = start if isinstance(start, datetime) else datetime.combine(start, datetime.now().time())
        self.offset = start - datetime.now()

    def now(self) -> datetime:
        return datetime.now() + self.offset


_CLOCK: Clock = SystemClock()


def clock_now() -> datetime:
    return _CLOCK.now()


def clock_today() -> date:
    return _CLOCK.today()


def get_clock() -> Clock:
    return _CLOCK


def set_clock(clock: Optional[Clock]) -> Clock:
    """시계 교체 → 이전 시계를 돌려줌 (None 이면 시스템 시계)"""
    global _CLOCK
    prev, _CLOCK = _CLOCK, clock or SystemClock()
    return prev


class frozen_clock:
    """with frozen_clock(date(...)) as clk: — 블록 안에서만 그 날짜로 고정"""

    def __init__(self, at):
        self.clock = FixedClock(at)

    def __enter__(self) -> FixedClock:
        self._prev = set_clock(self.clock)
        return self.clock

    def __exit__(self, *exc) -> None:
        set_clock(self._prev)


# ════════════════════════════════════════════════════════════════════
# 공통 상수
# ════════════════════════════════════════════════════════════════════
DOM_EQ = "국내주식"
FOR_EQ = "해외주식"
IG_BOND = "국채/우량채"
HY_BOND = "고위험채권"
COMMODITY = "원자재/금"
CRYPTO = "암호화폐"
CASH = "현금성자산"
ASSET_CLASSES = [DOM_EQ, FOR_EQ, IG_BOND, HY_BOND, COMMODITY, CRYPTO, CASH]

TAX_ADVANTAGED_ACCOUNTS = {"ISA", "연금저축", "IRP"}
OVERSEAS_TAX_FREE_LIMIT = 2_500_000        # 해외주식 양도차익 비과세(기본공제) 한도
MIN_DAILY_TRADING_VALUE = 1_000_000_000    # 리밸런싱 대상 ETF 최소 일 거래대금
REBALANCE_BAND = 5.0                       # ±5%p
REBALANCE_PERIOD_DAYS = 180
TRANSITION_TIMEOUT_DAYS = 180
TRADING_WINDOW = (dtime(10, 0), dtime(15, 0))


def clamp(x: float, lo: float = 0.0, hi: float = 100.0) -> float:
    return max(lo, min(hi, x))


def won(x: float) -> str:
    return f"{x:,.0f}원"


# ════════════════════════════════════════════════════════════════════
# STAGE 1. 재무 체력 측정 & 필수 비상금
# ════════════════════════════════════════════════════════════════════
class IncomeType(Enum):
    PUBLIC = ("정규직 공무원/공기업", 3, 3)
    REGULAR = ("일반 대기업/중소기업 정규직", 4, 5)
    FREELANCE = ("프리랜서/자영업자/계약직", 6, 9)
    UNEMPLOYED = ("무직/특수고용직", 12, 12)

    def __init__(self, label: str, m_min: int, m_max: int):
        self.label = label
        self.m_min = m_min
        self.m_max = m_max


def calc_buffer(income: float, expense: float) -> float:
    """재무 잉여율(%) = (월 고정 수입 - 월 필수 지출) / 월 고정 수입 × 100"""
    if income <= 0:
        return 0.0 if expense <= 0 else -100.0
    return (income - expense) / income * 100


@dataclass
class FinancialProfile:
    monthly_fixed_income: float          # Inc (정기)
    essential_expense: float             # Exp_essential (대출 원리금 포함)
    cash_current: float                  # C_current
    income_type: IncomeType
    monthly_irregular_income: float = 0.0
    existing_assets: float = 0.0         # V_existing
    secured_debt: float = 0.0            # 담보대출 잔액
    credit_debt: float = 0.0             # 신용대출 잔액
    monthly_debt_payment: float = 0.0    # 월 대출 원리금
    future_cf: float = 0.0               # CF_future
    future_cf_dday: Optional[int] = None # D-Day (일)
    m_multiplier: Optional[int] = None

    def __post_init__(self):
        if self.m_multiplier is None:
            self.m_multiplier = self.income_type.m_min
        elif not (self.income_type.m_min <= self.m_multiplier <= self.income_type.m_max):
            raise ValueError(
                f"{self.income_type.label}의 비상금 개월 수는 "
                f"{self.income_type.m_min}~{self.income_type.m_max}개월이어야 합니다.")

    @property
    def total_debt(self) -> float:
        return self.secured_debt + self.credit_debt

    @property
    def free_cash(self) -> float:
        return self.monthly_fixed_income - self.essential_expense

    @property
    def buffer(self) -> float:
        return calc_buffer(self.monthly_fixed_income, self.essential_expense)

    @property
    def dti(self) -> float:
        """DTI(%) = 월 대출 원리금 / 월 소득(정기+비정기) × 100"""
        income = self.monthly_fixed_income + self.monthly_irregular_income
        if income <= 0:
            return math.inf if self.monthly_debt_payment > 0 else 0.0
        return self.monthly_debt_payment / income * 100

    @property
    def adj_debt(self) -> float:
        return self.monthly_debt_payment * 2 if self.dti >= 40 else 0.0

    @property
    def c_reserve(self) -> float:
        return self.essential_expense * self.m_multiplier + self.adj_debt

    def summary(self) -> str:
        return "\n".join([
            f"  소득 유형           : {self.income_type.label} (비상금 {self.m_multiplier}개월)",
            f"  월 순 잉여금        : {won(self.free_cash)}",
            f"  재무 잉여율 Buffer  : {self.buffer:.1f}%",
            f"  DTI                 : {self.dti:.1f}%  → 위험 보정금 {won(self.adj_debt)}",
            f"  필수 비상금 C_reserve: {won(self.c_reserve)}",
            f"  현재 현금성 자산    : {won(self.cash_current)}",
        ])


# ════════════════════════════════════════════════════════════════════
# STAGE 2. 설문 & 2단계 가드레일 위험 성향
# ════════════════════════════════════════════════════════════════════
Q_ALLOWED = {
    "q1_1": (0, 25, 50, 75, 100),  # 손실 한도
    "q1_2": (0, 33, 66, 100),      # 시장 대응
    "q1_3": (0, 33, 66, 100),      # 수익/위험 선호
    "q2_1": (0, 25, 50, 75, 100),  # 투자 시한
    "q2_2": (0, 33, 66, 100),      # 자금 성격
}
TIER_NAMES = {1: "보수형", 2: "안정추구형", 3: "위험중립형", 4: "적극투자형", 5: "공격투자형"}


# ── 생애 목표 (나이·은퇴·주택 등 목표 시점) ─────────────────────────
# 목표까지 남은 기간은 해마다 줄어들므로, 연 1회 재평가 때 다시 계산해 등급·비중에 반영합니다.
GOAL_HORIZON_SCORE = ((0.5, 0), (1, 25), (3, 50), (5, 75))   # 남은 기간(년) 미만 → Horizon 점수 (Q2-1 보기와 같은 구간)
GOAL_TIER_CAP = ((1, 1), (3, 2), (5, 3), (10, 4))            # 남은 기간(년) 미만 → 그 목표 자금의 최대 Tier
RETIRED_TIER_CAP = 2            # 은퇴 이후(인출기) 노후 자금의 최대 Tier
RETIRED_HORIZON_SCORE = 50      # 은퇴 이후 노후 자금은 수십 년에 걸쳐 나눠 쓰므로 '1~3년' 수준으로 봄


def goal_horizon_score(years: float) -> float:
    for limit, score in GOAL_HORIZON_SCORE:
        if years < limit:
            return score
    return 100


def goal_tier_cap(years: float, retired: bool = False) -> int:
    if retired:
        return RETIRED_TIER_CAP
    for limit, tier in GOAL_TIER_CAP:
        if years < limit:
            return tier
    return 5


@dataclass(frozen=True)
class Goal:
    """은퇴 외 목표 (예: 주택 구입) — 목표 연도와 투자금 중 이 목표에 쓸 비율(%)"""
    name: str
    year: int
    share: float
    kind: str = ""               # 입력 칸 구분용 (예: "home", "other")


@dataclass
class GoalBucket:
    name: str
    share: float                 # 투자금 중 비율(%)
    years: Optional[int]         # 목표까지 남은 햇수 (None: 목표 시점 미정)
    retired: bool
    cap: int                     # 이 자금에 허용하는 최대 Tier

    def label(self) -> str:
        if self.years is None:
            when = "목표 시점 미정"
        elif self.retired:
            when = "은퇴 이후 인출기"
        else:
            when = f"{self.years}년 남음"
        cap = "제한 없음" if self.cap >= 5 else f"최대 Tier {self.cap} {TIER_NAMES[self.cap]}"
        return f"{self.name} {self.share:g}% · {when} → {cap}"


@dataclass
class LifeGoals:
    """
    나이와 목표 시점
      birth_year     : 출생 연도 (나이 = 올해 − 출생 연도)
      retirement_age : 은퇴 목표 나이 (없으면 나머지 자금은 '목표 시점 미정' 장기 자금)
      goals          : 은퇴 외 목표들 (Goal). 비율 합계는 100% 이하, 나머지는 은퇴(노후) 자금
    """
    birth_year: int
    retirement_age: Optional[int] = None
    goals: tuple = ()

    def __post_init__(self):
        self.goals = tuple(self.goals)
        if not 1900 <= self.birth_year <= clock_today().year:
            raise ValueError("출생 연도를 확인해 주세요.")
        if self.retirement_age is not None and not 30 <= self.retirement_age <= 90:
            raise ValueError("은퇴 목표 나이는 30~90세 사이로 입력해 주세요.")
        for g in self.goals:
            if not 0 < g.share <= 100:
                raise ValueError(f"{g.name} 비율은 0% 초과 100% 이하로 입력해 주세요.")
        if sum(g.share for g in self.goals) > 100 + 1e-9:
            raise ValueError("목표별 비율 합계가 100%를 넘을 수 없어요.")

    def age(self, today: date) -> int:
        return today.year - self.birth_year

    @property
    def retirement_year(self) -> Optional[int]:
        return None if self.retirement_age is None else self.birth_year + self.retirement_age

    def buckets(self, today: date) -> list:
        out = []
        for g in self.goals:
            yrs = max(0, g.year - today.year)
            out.append(GoalBucket(g.name, g.share, yrs, False, goal_tier_cap(yrs)))
        rest = 100 - sum(g.share for g in self.goals)
        if rest > 1e-9:
            if self.retirement_year is None:
                out.append(GoalBucket("장기 자금", rest, None, False, 5))
            else:
                yrs = self.retirement_year - today.year
                retired = yrs <= 0
                out.append(GoalBucket("노후 자금" if retired else "은퇴 자금", rest, max(0, yrs), retired,
                                      goal_tier_cap(max(0, yrs), retired)))
        return out

    def horizon_score(self, today: date, fallback: float) -> float:
        """목표 자금 비율로 가중한 Horizon 점수 (시점 미정 자금은 설문 Q2-1 점수 사용)"""
        total = 0.0
        for b in self.buckets(today):
            sc = fallback if b.years is None else RETIRED_HORIZON_SCORE if b.retired else goal_horizon_score(b.years)
            total += b.share / 100 * sc
        return total

    def passed(self, today: date) -> list:
        return [g.name for g in self.goals if g.year < today.year]

    def lines(self, today: date) -> list:
        head = f"나이 {self.age(today)}세" + (f" · 은퇴 목표 {self.retirement_age}세 ({self.retirement_year}년)"
                                           if self.retirement_age else "")
        out = [head] + ["  " + b.label() for b in self.buckets(today)]
        for name in self.passed(today):
            out.append(f"  ⚠ '{name}' 목표 연도가 지났어요. 성향 진단에서 목표를 갱신해 주세요.")
        return out


@dataclass
class SurveyAnswers:
    q1_1: int
    q1_2: int
    q1_3: int
    q2_1: int
    q2_2: int
    goals: Optional[LifeGoals] = None   # 나이·목표 시점 (없으면 설문만으로 Horizon 계산)

    def __post_init__(self):
        for key, allowed in Q_ALLOWED.items():
            if getattr(self, key) not in allowed:
                raise ValueError(f"{key} 응답은 {allowed} 중 하나여야 합니다.")

    @property
    def tol(self) -> float:
        return self.q1_1 * 0.40 + self.q1_2 * 0.35 + self.q1_3 * 0.25

    def horizon_q2_1(self, today: Optional[date] = None) -> float:
        """
        투자 기간 점수로 쓸 Q2-1 값: 목표 시점을 입력했으면 '목표까지 남은 기간 점수'와 설문 답 중 짧은 쪽
        (시간이 지나 목표가 가까워지면 연 1회 재평가 때 자동으로 낮아짐)
        """
        if self.goals is None:
            return float(self.q2_1)
        return min(float(self.q2_1), self.goals.horizon_score(today or clock_today(), self.q2_1))

    def horizon_at(self, today: Optional[date] = None) -> float:
        return self.horizon_q2_1(today) * 0.60 + self.q2_2 * 0.40

    @property
    def horizon(self) -> float:
        return self.horizon_at()


# Tier별 점수 구간: (하한 초과, 상한 이하]  — 소수 점수 포함
TIER_RANGES = {
    1: (-math.inf, 20.0),   # 0 이상 20 이하
    2: (20.0, 40.0),        # 20 초과 40 이하
    3: (40.0, 60.0),        # 40 초과 60 이하
    4: (60.0, 80.0),        # 60 초과 80 이하
    5: (80.0, math.inf),    # 80 초과 100 이하
}


def tier_range_label(tier: int) -> str:
    lo, hi = TIER_RANGES[tier]
    if tier == 1:
        return "0점 이상 ~ 20점 이하"
    if tier == 5:
        return "80점 초과 ~ 100점 이하"
    return f"{lo:.0f}점 초과 ~ {hi:.0f}점 이하"


def score_to_tier(score: float) -> int:
    """lo < score <= hi 인 Tier 반환 (예: 20.0 → Tier 1, 20.01 → Tier 2)"""
    for tier, (lo, hi) in TIER_RANGES.items():
        if lo < score <= hi:
            return tier
    raise ValueError(f"잘못된 점수: {score}")


def financial_cap(buffer: float) -> float:
    if buffer < 10:
        return 40
    if buffer < 20:
        return 60
    return 100


def psychological_cap(tol: float) -> float:
    if tol <= 20:
        return 20
    if tol <= 40:
        return 50
    return 100


def base_risk_score(tol: float, horizon: float, buffer: float) -> float:
    return 0.5 * tol + 0.2 * horizon + 0.3 * clamp(buffer)


@dataclass
class RiskProfile:
    tol: float
    horizon: float
    buffer: float
    base: float
    cap_financial: float
    cap_psychological: float
    final: float
    tier: int

    @property
    def tier_name(self) -> str:
        return TIER_NAMES[self.tier]

    def summary(self) -> str:
        return "\n".join([
            f"  Tol={self.tol:.1f}  Horizon={self.horizon:.1f}  Buffer={self.buffer:.1f}%",
            f"  RiskScore_base={self.base:.1f}  Cap_fin={self.cap_financial:.0f}  "
            f"Cap_psy={self.cap_psychological:.0f}",
            f"  RiskScore_final={self.final:.2f} → Tier {self.tier} ({self.tier_name}, "
            f"{tier_range_label(self.tier)})",
        ])


def assess_risk(survey: SurveyAnswers, buffer: float, today: Optional[date] = None) -> RiskProfile:
    """today: 목표까지 남은 기간을 계산할 기준일 (연 1회 재평가 때는 재평가 시점)"""
    tol, hor = survey.tol, survey.horizon_at(today)
    base = base_risk_score(tol, hor, buffer)
    cf, cp = financial_cap(buffer), psychological_cap(tol)
    final = min(base, cf, cp)
    return RiskProfile(tol, hor, buffer, base, cf, cp, final, score_to_tier(final))


# ── Tier별 모델 포트폴리오 ─────────────────────────────────────────
@dataclass(frozen=True)
class ModelPortfolio:
    key: str
    name: str
    items: tuple  # ((세부 종목, 자산군, 비중%), ...)
    purpose: str

    @property
    def targets(self) -> dict:
        t = {c: 0.0 for c in ASSET_CLASSES}
        for _, cls, w in self.items:
            t[cls] += w
        return t


MODEL_PORTFOLIOS = {
    1: ModelPortfolio("T1", "Tier 1 보수형", (
        ("미국 대형 배당주/배당성장 ETF", FOR_EQ, 10),
        ("단기 국채", IG_BOND, 40), ("우량 회사채", IG_BOND, 20),
        ("MMF/파킹통장/단기 예적금", CASH, 30)),
        "원금 손실 극도 방지, 이자·고배당 중심 현금 흐름"),
    2: ModelPortfolio("T2", "Tier 2 안정추구형", (
        ("S&P500 ETF", FOR_EQ, 20), ("글로벌 배당주 ETF", FOR_EQ, 10),
        ("중기 국채", IG_BOND, 30), ("종합채권 ETF", IG_BOND, 20),
        ("금 ETF", COMMODITY, 5), ("CMA/파킹통장", CASH, 15)),
        "채권 기반 + 글로벌 대형주로 인플레이션 방어"),
    3: ModelPortfolio("T3", "Tier 3 위험중립형", (
        ("S&P500", FOR_EQ, 30), ("글로벌 선진국/배당주", FOR_EQ, 20),
        ("중장기 국채", IG_BOND, 25), ("우량 회사채", IG_BOND, 10),
        ("금/원자재 ETF", COMMODITY, 10), ("단기 파킹통장", CASH, 5)),
        "60:40 변형, 시장 성장 참여 + 금 인플레이션 헤지"),
    4: ModelPortfolio("T4", "Tier 4 적극투자형", (
        ("S&P500", FOR_EQ, 40), ("나스닥100/성장주", FOR_EQ, 20),
        ("신흥국/테마 ETF", FOR_EQ, 10),
        ("장기 미국 국채", IG_BOND, 15), ("하이일드 채권", HY_BOND, 5),
        ("금/부동산 REITs", COMMODITY, 5), ("단기 자금", CASH, 5)),
        "성장 자산 집중 + 장기채 분산"),
    5: ModelPortfolio("T5", "Tier 5 공격투자형", (
        ("나스닥100", FOR_EQ, 40), ("S&P500", FOR_EQ, 25),
        ("혁신기술/테마주", FOR_EQ, 20),
        ("비트코인/가상자산 ETF", CRYPTO, 5), ("원자재/금", COMMODITY, 5),
        ("스마트 바이 대기 현금", CASH, 5)),
        "-20% 이상 하락 감내, 장기 자본이득 극대화"),
}


def goal_blended_targets(tier: int, goals: Optional[LifeGoals], today: Optional[date] = None) -> dict:
    """
    목표별 자금 비율대로 모델 포트폴리오를 섞은 목표 비중 (글라이드 패스)
      목표 자금마다 적용 Tier = min(투자 등급, 남은 기간에 따른 최대 Tier)
      예) Tier 4, 주택 자금 30%(2년 남음 → 최대 Tier 2) + 은퇴 자금 70%(25년 남음)
          → 0.3 × Tier 2 비중 + 0.7 × Tier 4 비중
    """
    if goals is None:
        return MODEL_PORTFOLIOS[tier].targets
    t = {c: 0.0 for c in ASSET_CLASSES}
    for b in goals.buckets(today or clock_today()):
        for c, w in MODEL_PORTFOLIOS[min(tier, b.cap)].targets.items():
            t[c] += w * b.share / 100
    return {c: round(v, 4) for c, v in t.items()}


# Trigger B-2 전용 비상 포트폴리오
TIER1_LIQUID = ModelPortfolio("T1-L", "Tier 1 보수형(유동성 보강)", (
    ("배당/대형주", FOR_EQ, 10), ("국채/우량채", IG_BOND, 50), ("현금성", CASH, 40)),
    "Tier 2 → Tier 1 하향 시 현금 유동성 보강")
TIER1_ULTRA_SAFE = ModelPortfolio("T1-U", "Tier 1 Ultra-Safe", (
    ("국채/우량채", IG_BOND, 40), ("현금성", CASH, 60)),
    "Tier 1 보수형의 비상 비중")


# Trigger B-1 전용 포트폴리오 (현금 최우선, 대체자산 0%, 채권은 만기 3개월 미만 단기채 위주)
SHORT_BOND_MAX_MONTHS = 3       # 단기채 기준: 잔존만기 3개월 미만
SHORT_BOND_KEY = "단기채"       # instruments 에서 단기채 대표 종목 키

B1_TIER2 = ModelPortfolio("B1-T2", "B-1 Tier 2 (현금 우선)", (
    ("주식(대형·배당)", FOR_EQ, 10), ("단기 국채(만기 3개월 미만)", IG_BOND, 40), ("현금성", CASH, 50)),
    "B-1 Hard Stop: Buffer 5~10% — 현금 50% 최우선, 채권은 단기채 위주")
B1_TIER1 = ModelPortfolio("B1-T1", "B-1 Tier 1 (현금 최우선)", (
    ("단기 국채(만기 3개월 미만)", IG_BOND, 30), ("현금성", CASH, 70)),
    "B-1 Hard Stop: Buffer 5% 미만 — 현금 70% 최우선, 채권은 단기채 위주")


def is_short_bond(h) -> bool:
    """만기 3개월 미만 단기채 여부 (만기 미입력 채권은 장기로 간주)"""
    return (h.asset_class == IG_BOND and h.maturity_months is not None
            and h.maturity_months < SHORT_BOND_MAX_MONTHS)
B1_PORTFOLIOS = {1: B1_TIER1, 2: B1_TIER2}


def with_cash_floor(targets: dict, floor: float) -> dict:
    """현금성 자산 비중을 최소 floor%로 올리고 나머지를 비례 축소"""
    if targets[CASH] >= floor:
        return dict(targets)
    rest = 100 - targets[CASH]
    scale = (100 - floor) / rest if rest > 0 else 0
    new = {c: (w * scale if c != CASH else floor) for c, w in targets.items()}
    return new


# ════════════════════════════════════════════════════════════════════
# STAGE 3. 자산 표준화 & 시가 평가
# ════════════════════════════════════════════════════════════════════
@dataclass
class Holding:
    ticker: str
    name: str
    asset_class: str
    quantity: float
    price: float                    # 현재가
    avg_price: float = 0.0          # 매수 단가
    settlement_days: int = 2        # T+N
    volatility: float = 0.0         # 연 변동성(%)
    tax_rate: float = 0.0           # 양도차익 세율 (해외 0.22 등)
    fee_rate: float = 0.00015
    account: str = "일반"
    overseas: bool = False
    locked: bool = False            # 사용자 매도 금지
    daily_trading_value: float = math.inf
    fractional: bool = False        # 소수 단위 거래 가능 (암호화폐 등)
    product_type: str = "ETF"       # "ETF" / "주식" (국내 개별 주식은 증권거래세 대상)
    maturity_months: Optional[float] = None   # 채권: 잔존만기(또는 듀레이션) 개월, 미입력 시 장기로 간주

    def __post_init__(self):
        if self.asset_class in (CRYPTO, CASH):
            self.fractional = True
        if self.asset_class not in ASSET_CLASSES:
            raise ValueError(f"알 수 없는 자산군: {self.asset_class}")
        if self.avg_price <= 0:
            self.avg_price = self.price

    @property
    def value(self) -> float:
        return self.quantity * self.price

    @property
    def profit_pct(self) -> float:
        return (self.price / self.avg_price - 1) * 100 if self.avg_price else 0.0

    @property
    def tax_advantaged(self) -> bool:
        return self.account in TAX_ADVANTAGED_ACCOUNTS

    @property
    def market(self) -> Optional[str]:
        """정산일 계산 시장: 한국·미국 (정산 0일 자산은 None)"""
        return asset_market(self.overseas, self.settlement_days)

    def gain_ratio(self) -> float:
        """매도금액 중 양도차익 비율"""
        return max(0.0, 1 - self.avg_price / self.price) if self.price > 0 else 0.0

    def estimate_tax(self, amount: float, realized_overseas_ytd: float = 0.0) -> float:
        """매도 세금 추정 — 해외주식은 비과세 한도(250만 원) 반영 (estimate_sell_tax 참조)"""
        return estimate_sell_tax(self, amount, realized_overseas_ytd)

    def estimate_fee(self, amount: float) -> float:
        return amount * self.fee_rate


@dataclass
class Instrument:
    """자산군별 대표 매수 종목"""
    ticker: str
    name: str
    asset_class: str
    price: float
    settlement_days: int = 2
    fee_rate: float = 0.00015
    daily_trading_value: float = math.inf
    tax_rate: float = 0.0
    overseas: bool = False
    account: str = "일반"
    maturity_months: Optional[float] = None
    product_type: str = "ETF"


@dataclass
class Order:
    side: str             # "매도" / "매수"
    ticker: str
    name: str
    asset_class: str
    quantity: float
    price: float
    day: int = 0          # T+day 에 집행
    reason: str = ""
    purpose: str = ""     # 매도 목적: 매수 재원 / 유동성 확보 / 위험 축소 / 사용자 요청
    account: str = ""     # 매수 계좌 (절세 계좌 우선 배정)
    deadline_days: Optional[int] = None   # 목돈 지출까지 남은 영업일 (SettleDeadline 이면 날짜로 판단)
    exec_date: Optional[date] = None      # 실제 집행일 (schedule_orders: 주말·휴장일 반영)
    cash_date: Optional[date] = None      # 매도 대금을 원화로 쓸 수 있는 날 (매도 주문만)

    @property
    def amount(self) -> float:
        return self.quantity * self.price

    def __str__(self) -> str:
        if self.asset_class == CASH:
            qty = "이체"
        elif float(self.quantity).is_integer():
            qty = f"{self.quantity:,.0f}주"
        else:
            qty = f"{self.quantity:,.4f}개"
        tag = f" 〔{self.purpose}〕" if self.purpose else ""
        if self.account and self.asset_class != CASH and self.side == "매수":
            tag += f" [{self.account}]"
        when = f"{_md(self.exec_date)} · T+{self.day}" if self.exec_date else f"T+{self.day}"
        if self.cash_date and self.side == "매도" and self.cash_date != self.exec_date:
            tag += f" → 대금 {_md(self.cash_date)}"
        return (f"[{when}] {self.side} {self.name}({self.asset_class}) "
                f"{qty} ≈ {won(self.amount)}  {self.reason}{tag}")


@dataclass
class Portfolio:
    holdings: list = field(default_factory=list)

    def class_values(self) -> dict:
        v = {c: 0.0 for c in ASSET_CLASSES}
        for h in self.holdings:
            v[h.asset_class] += h.value
        return v

    def total(self) -> float:
        return sum(h.value for h in self.holdings)

    def current_ratios(self) -> dict:
        tot = self.total()
        cv = self.class_values()
        return {c: (cv[c] / tot * 100 if tot else 0.0) for c in ASSET_CLASSES}

    def gaps(self, targets: dict) -> dict:
        cur = self.current_ratios()
        return {c: cur[c] - targets.get(c, 0.0) for c in ASSET_CLASSES}

    def find(self, ticker: str) -> Optional[Holding]:
        return next((h for h in self.holdings if h.ticker == ticker), None)

    def apply(self, orders: list, instruments: dict | None = None) -> "Portfolio":
        """주문 체결을 시뮬레이션한 새 포트폴리오 반환"""
        p = copy.deepcopy(self)
        instruments = instruments or {}
        for o in orders:
            h = p.find(o.ticker)
            if o.side == "매도":
                if h:
                    h.quantity = max(0.0, h.quantity - o.quantity)
            else:
                if h:
                    new_qty = h.quantity + o.quantity
                    if new_qty > 0:
                        h.avg_price = (h.avg_price * h.quantity + o.price * o.quantity) / new_qty
                    h.quantity = new_qty
                else:
                    inst = next((i for i in instruments.values() if i.ticker == o.ticker), None)
                    p.holdings.append(Holding(
                        o.ticker, o.name, o.asset_class, o.quantity, o.price, o.price,
                        settlement_days=inst.settlement_days if inst else 2,
                        fee_rate=inst.fee_rate if inst else 0.00015,
                        tax_rate=inst.tax_rate if inst else 0.0,
                        overseas=inst.overseas if inst else False,
                        account=o.account or (inst.account if inst else "일반"),
                        product_type=inst.product_type if inst else "ETF",
                        daily_trading_value=inst.daily_trading_value if inst else math.inf,
                        maturity_months=inst.maturity_months if inst else None))
        p.holdings = [h for h in p.holdings if h.quantity > 1e-9]
        return p

    def report(self, targets: dict | None = None) -> str:
        cur = self.current_ratios()
        cv = self.class_values()
        lines = [f"  총 평가액 {won(self.total())}",
                 f"  {'자산군':<10}{'평가액':>16}{'현재%':>9}" + (f"{'목표%':>9}{'Gap%p':>9}" if targets else "")]
        for c in ASSET_CLASSES:
            if cv[c] == 0 and not (targets and targets.get(c)):
                continue
            line = f"  {c:<10}{won(cv[c]):>16}{cur[c]:>9.1f}"
            if targets:
                line += f"{targets.get(c, 0):>9.1f}{cur[c] - targets.get(c, 0):>+9.1f}"
            lines.append(line)
        return "\n".join(lines)


# ── 공용 매매 헬퍼 ─────────────────────────────────────────────────
# 매도 목적 (가계부 연속 미입력 시 '매수 재원' 매도만 보류)
PURPOSE_FUNDING = "매수 재원"      # 비중 미달 자산 매수 자금 마련 (리밸런싱·전환 매매)
PURPOSE_LIQUIDITY = "유동성 확보"  # 비상금 복구·목돈 지출 대비 (Trigger A·C)
PURPOSE_RISK = "위험 축소"         # 등급 하향에 따른 위험 자산 축소·단기채 교체 (B-1·B-2)
PURPOSE_USER = "사용자 요청"       # 사용자가 직접 요청한 매매


def _sell_order(h: Holding, amount: float, day: int, reason: str, round_up: bool,
                purpose: str = PURPOSE_FUNDING) -> Optional[Order]:
    if amount <= 0 or h.quantity <= 0:
        return None
    if h.fractional:
        qty = min(h.quantity, amount / h.price)
    else:
        raw = amount / h.price
        qty = math.ceil(raw) if round_up else math.floor(raw)
        qty = min(h.quantity, qty)
    if qty <= 0:
        return None
    return Order("매도", h.ticker, h.name, h.asset_class, qty, h.price, day, reason, purpose)


def _cash_order(amount: float, instruments: dict, day: int, reason: str) -> Optional[Order]:
    if amount <= 0.5:
        return None
    inst = instruments.get(CASH)
    ticker, name = (inst.ticker, inst.name) if inst else ("CMA", "CMA/파킹통장")
    return Order("매수", ticker, name, CASH, amount, 1.0, day, reason)


def allocate_buys(budget: float, weights: dict, instruments: dict, day: int, reason: str):
    """
    예산을 자산군 가중치대로 매수 주문으로 변환.
    - 최소 주문 단위 가드: 1주 가격 미만이면 매수 유예(Skip)
    - 거래대금 가드: 일 거래대금 10억 미만 ETF 제외
    - 남는 자투리(Dust Cash)는 CMA/파킹통장으로 흡수
    """
    orders, notes = [], []
    total_w = sum(w for w in weights.values() if w > 0)
    if budget <= 0 or total_w <= 0:
        return orders, notes
    dust = 0.0
    for cls, w in weights.items():
        if w <= 0:
            continue
        amt = budget * w / total_w
        if cls == CASH:
            dust += amt
            continue
        inst = instruments.get(cls)
        if inst is None:
            notes.append(f"{cls}: 대표 종목 미지정 → 현금 대기")
            dust += amt
            continue
        if inst.daily_trading_value < MIN_DAILY_TRADING_VALUE:
            notes.append(f"{inst.name}: 일 거래대금 10억 미만 → 매수 제외")
            dust += amt
            continue
        qty = math.floor(amt / inst.price)
        if qty < 1:
            notes.append(f"{inst.name}: 배정액 {won(amt)} < 1주 가격 {won(inst.price)} → 매수 유예(Skip)")
            dust += amt
            continue
        orders.append(Order("매수", inst.ticker, inst.name, cls, qty, inst.price, day, reason,
                            account=inst.account))
        dust += amt - qty * inst.price
    co = _cash_order(dust, instruments, day, "자투리/현금 비중 → CMA 흡수")
    if co:
        orders.append(co)
    return orders, notes


# ════════════════════════════════════════════════════════════════════
# STAGE 3 - 경로 B / 전략 A. 즉시 리밸런싱
# ════════════════════════════════════════════════════════════════════
OVERSEAS_TAX_RATE = 0.22          # 해외주식 양도소득세율(지방세 포함)
STRATEGY_B_COST_RATIO = 1.0       # 예상 세금·수수료가 총자산의 1% 이상이면 전략 B 권유
STRATEGY_B_LOSS_RATIO = 5.0       # 확정될 손실이 총자산의 5% 이상이면 전략 B 권유


def locked_adjusted_targets(portfolio: Portfolio, targets: dict) -> dict:
    """
    매도 금지(고정) 자산을 반영한 목표 비중.
    고정 자산 평가액이 목표 금액을 넘는 자산군은 고정 금액을 그대로 인정하고,
    남은 금액을 나머지 자산군에 원래 목표 비율대로 재배분합니다.
    """
    total = portfolio.total()
    if total <= 0:
        return dict(targets)
    locked_val = {c: 0.0 for c in ASSET_CLASSES}
    for h in portfolio.holdings:
        if h.locked:
            locked_val[h.asset_class] += h.value
    fixed: dict = {}
    while True:
        free = [c for c in ASSET_CLASSES if c not in fixed]
        remaining = total - sum(fixed.values())
        wsum = sum(targets.get(c, 0) for c in free)
        if wsum > 0:
            amounts = {c: remaining * targets.get(c, 0) / wsum for c in free}
        else:
            amounts = {c: (remaining if c == CASH else 0.0) for c in free}
        newly = [c for c in free if locked_val[c] > amounts[c] + 1e-9]
        if not newly:
            break
        for c in newly:
            fixed[c] = locked_val[c]
    amounts.update(fixed)
    return {c: amounts.get(c, 0.0) / total * 100 for c in ASSET_CLASSES}


@dataclass
class SellCostSummary:
    """전략 A 주문서에 표시할 세금·수수료·확정 손실 정보"""
    total_asset: float
    overseas_net_gain: float
    overseas_tax: float
    overseas_tax_without_netting: float
    other_tax: float
    fees: float
    realized_losses: list          # [(종목명, 손실액)]

    @property
    def total_cost(self) -> float:
        return self.overseas_tax + self.other_tax + self.fees

    @property
    def realized_loss_total(self) -> float:
        return sum(l for _, l in self.realized_losses)

    @property
    def cost_ratio(self) -> float:
        return self.total_cost / self.total_asset * 100 if self.total_asset else 0.0

    @property
    def loss_ratio(self) -> float:
        return self.realized_loss_total / self.total_asset * 100 if self.total_asset else 0.0

    def strategy_b_advice(self) -> Optional[str]:
        reasons = []
        if self.cost_ratio >= STRATEGY_B_COST_RATIO:
            reasons.append(f"예상 세금·수수료가 총자산의 {self.cost_ratio:.2f}%")
        if self.loss_ratio >= STRATEGY_B_LOSS_RATIO:
            reasons.append(f"확정 손실이 총자산의 {self.loss_ratio:.2f}%")
        if not reasons:
            return None
        return "⚠ " + ", ".join(reasons) + " → 전략 B(점진적 리밸런싱)가 더 적합할 수 있습니다."

    def lines(self) -> list:
        out = [f"예상 세금 {won(self.overseas_tax + self.other_tax)} "
               f"(해외 {won(self.overseas_tax)}, 기타 {won(self.other_tax)}) / 수수료 {won(self.fees)}"]
        saved = self.overseas_tax_without_netting - self.overseas_tax
        if saved > 0:
            out.append(f"해외주식 손익 상계로 절감되는 세금 ≈ {won(saved)}")
        if self.realized_losses:
            out.append(f"매도로 확정되는 손실 합계 {won(self.realized_loss_total)} — "
                       + ", ".join(f"{n} {won(l)}" for n, l in self.realized_losses))
            out.append("※ 손실 확정 매도가 포함되어 있어 사용자 승인이 필요합니다.")
        advice = self.strategy_b_advice()
        if advice:
            out.append(advice)
        return out


def summarize_sell_costs(portfolio: Portfolio, sells: list, buys: list,
                         realized_overseas_gain_ytd: float = 0.0) -> SellCostSummary:
    net = pos = other_tax = fees = 0.0
    losses = []
    for o in sells:
        h = portfolio.find(o.ticker)
        if h is None or h.asset_class == CASH:
            continue
        gain = o.amount * (1 - h.avg_price / h.price) if h.price else 0.0
        fees += h.estimate_fee(o.amount)
        if gain < 0:
            losses.append((h.name, -gain))
        if h.tax_advantaged:
            continue
        if h.overseas:
            net += gain
            pos += max(gain, 0.0)
        else:
            other_tax += max(gain, 0.0) * h.tax_rate
    fees += sum(o.amount * 0.00015 for o in buys if o.asset_class != CASH)

    def overseas_tax(extra: float) -> float:
        before = max(0.0, realized_overseas_gain_ytd - OVERSEAS_TAX_FREE_LIMIT)
        after = max(0.0, realized_overseas_gain_ytd + extra - OVERSEAS_TAX_FREE_LIMIT)
        return max(0.0, after - before) * OVERSEAS_TAX_RATE

    return SellCostSummary(portfolio.total(), net, overseas_tax(net), overseas_tax(pos),
                           other_tax, fees, losses)


@dataclass
class RestructuringPlan:
    trade_amounts: dict
    adjusted_targets: dict
    sell_orders: list
    buy_orders: list
    settle_day: int
    notes: list
    cost: SellCostSummary
    withdrawn: float = 0.0          # 비상금/지출 대기 계좌로 빠져나가는 매도 대금
    uncovered_need: float = 0.0     # 매도 대금으로 못 채운 필요 현금

    @property
    def orders(self) -> list:
        return self.sell_orders + self.buy_orders


def restructuring_orders(portfolio: Portfolio, targets: dict, instruments: dict, *,
                         hold_buys: bool = False, safe_only: bool = False,
                         cash_need: float = 0.0,
                         realized_overseas_gain_ytd: float = 0.0,
                         equity_rotation: bool = False,
                         sell_deadline_days: Optional[int] = None) -> RestructuringPlan:
    """
    Step 1 일괄 교체 주문서.
    - 매도 금지 자산은 팔지 않고, 나머지 자산으로 목표 비중 재배분
    - 손실 자산도 유예 없이 매도하되 확정 손실을 주문서에 표시
    - hold_buys  : Trigger A·C·B-1 → 매수 동결, 매도 대금은 현금 대기
    - safe_only  : Trigger B-2   → 채권·현금성 자산만 매수
    - cash_need  : Trigger A·C 부족 현금 → 매도 대금에서 우선 인출
    """
    adj = locked_adjusted_targets(portfolio, targets)
    total = portfolio.total()
    cv = portfolio.class_values()
    trade = {c: total * adj[c] / 100 - cv[c] for c in ASSET_CLASSES}
    notes = []
    locked = [h.name for h in portfolio.holdings if h.locked]
    if locked:
        notes.append("매도 금지 자산 유지: " + ", ".join(locked) + " → 나머지 자산으로 목표 비중 재배분")

    # Phase 2-1: 비중 초과 자산 매도 (매도 금지 제외, 보유 종목 비례)
    sells = []
    for c, t in trade.items():
        if t >= 0:
            continue
        cands = [h for h in portfolio.holdings if h.asset_class == c and not h.locked
                 and settles_in_time(h, sell_deadline_days)]
        cand_val = sum(h.value for h in cands)
        for h in cands:
            o = _sell_order(h, -t * h.value / cand_val, 0, "전략A 비중 초과 매도", round_up=False,
                            purpose=_plan_sell_purpose(cash_need, safe_only))
            if o:
                sells.append(o)
    settle = max((portfolio.find(o.ticker).settlement_days for o in sells if o.asset_class != CASH), default=0)

    # 매도 대금 행선지: 부족 현금 우선 → 매수 동결/안전자산/평시 매수 (STAGE 4 규칙)
    weights = {c: t for c, t in trade.items() if t > 0}
    buys, n, withdrawn, uncovered = _route_proceeds(
        sum(o.amount for o in sells), weights, instruments, settle,
        hold_buys=hold_buys, safe_only=safe_only, cash_need=cash_need, reason="전략A 비중 미달 매수",
        purpose=_plan_sell_purpose(cash_need, safe_only),
        **(dict(equity_budget=sum(o.amount for o in sells if o.asset_class in EQUITY_CLASSES),
                equity_deficits={c: t for c, t in trade.items() if c in EQUITY_CLASSES and t > 0})
           if equity_rotation else {}))
    notes += n

    cost = summarize_sell_costs(portfolio, sells, buys, realized_overseas_gain_ytd)
    return RestructuringPlan(trade, adj, sells, buys, settle, notes, cost, withdrawn, uncovered)


def _cash_ticker(instruments: dict) -> tuple:
    inst = instruments.get(CASH)
    return (inst.ticker, inst.name) if inst else ("CMA", "CMA/파킹통장")


def precision_check(portfolio: Portfolio, targets: dict, threshold: float = 1.0) -> tuple:
    """정밀도 검증: 매도 금지 자산을 반영한 목표 비중 기준"""
    adj = locked_adjusted_targets(portfolio, targets)
    gaps = portfolio.gaps(adj)
    bad = {c: g for c, g in gaps.items() if abs(g) > threshold}
    return (len(bad) == 0, bad)


# ════════════════════════════════════════════════════════════════════
# STAGE 3 - 경로 B / 전략 B. 점진적 리밸런싱 (Soft Migration)
# ════════════════════════════════════════════════════════════════════
DEFER_BIG_LOSS = -15.0        # 큰 손실 기준(%)
GRADUAL_EXIT_RULES = ((0.0, 0.5), (-5.0, 0.2))   # (수익률 이상, 매도 비율): 본전 50%, -5% 이내 20%
SOFT_THRESHOLD = 3.0          # 전략 B 완료 비중 오차(±%p)


@dataclass
class SoftMigrationState:
    targets: dict                                         # 등급 목표 비중 (트리거로 바뀔 수 있음)
    deferred: dict = field(default_factory=dict)          # ticker → 유예 사유
    locked: set = field(default_factory=set)
    realized_overseas_net: float = 0.0                    # 올해 해외주식 실현 손익(손실 포함, 상계용)
    initial_done: bool = False

    @property
    def tax_room(self) -> float:
        """손익 상계 반영 비과세 여유: 손실이 실현되면 여유가 늘어남"""
        return max(0.0, OVERSEAS_TAX_FREE_LIMIT - self.realized_overseas_net)


@dataclass
class SoftPlan:
    sell_orders: list
    buy_orders: list
    notes: list
    withdrawn: float = 0.0
    uncovered_need: float = 0.0
    overseas_net: float = 0.0       # 이번 매도로 실현되는 해외주식 손익(부호 포함)
    is_initial: bool = False

    @property
    def orders(self) -> list:
        return self.sell_orders + self.buy_orders


def _overseas_gain(h: Holding, amount: float) -> float:
    if not h.overseas or h.tax_advantaged or h.price <= 0:
        return 0.0
    return amount * (1 - h.avg_price / h.price)


def _tax_limited_amount(h: Holding, amount: float, room: float) -> float:
    """해외주식: 남은 비과세 여유(손익 상계 반영) 안에서만 매도"""
    if not h.overseas or h.tax_advantaged:
        return amount
    gr = h.gain_ratio()
    if gr <= 0:
        return amount
    return min(amount, room / gr)


B2_EXIT_RATIO = 0.5    # B-2: 비중 초과 위험 자산의 초과분 중 매달 매도할 비율


def b2_gradual_exit(portfolio: Portfolio, targets: dict, *, exclude: set = frozenset(),
                    tax_room: float = math.inf, label: str = "B-2",
                    keep_classes: tuple = (IG_BOND, CASH)) -> tuple:
    """
    Trigger B-2 Gradual Exit (STAGE 4 규칙, 정식 관리 모드·전략 B 공용)
    등급 하향으로 비중 초과가 된 위험 자산(주식·대체·고위험채·암호화폐) 중
    수익권(본전 이상) 종목만, 초과분의 B2_EXIT_RATIO씩 매달 매도 → 대금은 안전 자산으로.
    손실 종목은 매도하지 않고 잉여 현금 희석에 맡깁니다.
    매도 순서: 절세 계좌 → CostPenal_i(세금·수수료 부담) 낮은 순 / 같으면 수익률 높은 순.
    반환: (매도 주문, 안내, 해외 실현 손익)
    """
    adj = locked_adjusted_targets(portfolio, targets)
    total = portfolio.total()
    gaps = portfolio.gaps(adj)
    sells, notes = [], []
    room, net = tax_room, 0.0
    for c, g in gaps.items():
        if g <= 0 or c in keep_classes:
            continue
        to_sell = total * g / 100 * B2_EXIT_RATIO
        pool = [h for h in portfolio.holdings
                if h.asset_class == c and not h.locked and h.ticker not in exclude]
        cands = sorted([h for h in pool if h.profit_pct >= 0],
                       key=lambda h: tax_aware_sell_key(h, min(to_sell, h.value)) + (-h.profit_pct,))
        losers = [h.name for h in pool if h.profit_pct < 0]
        if losers:
            notes.append(f"{label} 매도 보류(손실 중): {', '.join(losers)} → 수익권 회복 시 단계적 매도")
        for h in cands:
            if to_sell <= 0:
                break
            want = min(to_sell, h.value)
            amt = _tax_limited_amount(h, want, room)
            if amt < want:
                notes.append(f"{h.name}: 해외주식 비과세 여유로 매도 {won(amt)}까지 제한")
            o = _sell_order(h, amt, 0,
                            f"{label} 단계적 비중 조정 매도 (초과분 {int(B2_EXIT_RATIO * 100)}%, 수익률 {h.profit_pct:.1f}%)",
                            round_up=False, purpose=PURPOSE_RISK)
            if o:
                sells.append(o)
                to_sell -= o.amount
                g_ = _overseas_gain(h, o.amount)
                net += g_
                room = max(0.0, room - g_)
    return sells, notes, net


def soft_migration_analysis(portfolio: Portfolio, targets: dict) -> SoftMigrationState:
    """
    Step 1: 3대 필터
    - 고정 자산: 사용자 매도 금지
    - 유예 자산: 비중 초과 자산군에 속한 손실 종목 → 매도 유예, 잉여 현금으로 희석
        · 큰 손실(≤ -15%)      : 회복될 때까지 매도 유예
        · 소폭 손실(-15% ~ 0%) : 같은 규칙으로 유예 (-5% 이내부터 단계적 매도)
    - 세금: 해외주식은 손익 상계 후 비과세 한도 안에서만 매도 (Step 2·3에서 적용)
    """
    st = SoftMigrationState(targets)
    gaps = portfolio.gaps(locked_adjusted_targets(portfolio, targets))
    for h in portfolio.holdings:
        if h.locked:
            st.locked.add(h.ticker)
        elif h.asset_class != CASH and gaps[h.asset_class] > 0 and h.profit_pct < 0:
            kind = "큰 손실" if h.profit_pct <= DEFER_BIG_LOSS else "소폭 손실"
            st.deferred[h.ticker] = f"{kind} {h.profit_pct:.1f}%"
    return st


EQUITY_CLASSES = (DOM_EQ, FOR_EQ)


def _plan_sell_purpose(cash_need: float, safe_only: bool) -> str:
    """전환·리밸런싱 계획의 매도 목적: 부족 현금 충당 → 유동성 / B-2 → 위험 축소 / 그 외 → 매수 재원"""
    if cash_need > 0:
        return PURPOSE_LIQUIDITY
    if safe_only:
        return PURPOSE_RISK
    return PURPOSE_FUNDING


def _route_proceeds(budget_in: float, weights: dict, instruments: dict, day: int, *,
                    hold_buys: bool, safe_only: bool, cash_need: float, reason: str,
                    equity_budget: float = 0.0, equity_deficits: Optional[dict] = None,
                    purpose: str = PURPOSE_FUNDING) -> tuple:
    """
    매도 대금·투입 현금의 행선지 결정 (전략 A·B·정식 관리 모드 공용, STAGE 4 트리거 규칙)
    ① Trigger A·C 부족 현금 우선 인출 ② A·C·B-1 매수 동결 → 현금 대기
    ③ B-2 → 채권·현금성만 매수, 주식 몫은 현금 대기
       (B-1 회복 Path 2로 등급이 바뀐 경우: 주식 매도 대금(equity_budget) 한도 안에서만
        비중 미달 주식 자산군을 매수해 주식 비중 조정 — 신규 현금의 주식 추가 매수는 불가)
    ④ 평시 → 미달 자산 매수
    반환: (매수 주문, 안내, 인출액, 못 채운 필요 현금)
    """
    notes = []
    withdrawn = min(cash_need, budget_in)
    budget = budget_in - withdrawn
    if withdrawn > 0:
        notes.append(f"매도 대금 {won(withdrawn)} → 비상금 계좌/지출 대기 계좌로 우선 이체")
    ticker, name = _cash_ticker(instruments)
    weights = {c: w for c, w in weights.items() if w > 0}
    if hold_buys or not weights:
        buys = []
        if budget > 0.5:
            why = "매수 동결 → 현금 대기" if hold_buys else "매수 대상 없음 → 현금 대기"
            buys.append(Order("매수", ticker, name, CASH, budget, 1.0, day, why, purpose))
            if hold_buys:
                notes.append(f"트리거로 매수 동결 → {won(budget)} 현금 대기 (해제 후 재정렬)")
    elif safe_only:
        buys = []
        eq_def = {c: a for c, a in (equity_deficits or {}).items() if a > 0 and c in EQUITY_CLASSES}
        eq_amt = min(equity_budget, budget, sum(eq_def.values())) if eq_def else 0.0
        if eq_amt > 0.5:
            eq_buys, n = allocate_buys(eq_amt, eq_def, instruments, day,
                                       "Path 2 주식 비중 조정(주식 매도 대금 한도)")
            buys += eq_buys
            notes += n
            notes.append(f"Path 2 주식 비중 조정: 주식 매도 대금 중 {won(eq_amt)}로 비중 미달 주식 매수 "
                         f"(신규 현금의 주식 추가 매수 불가)")
            budget -= eq_amt
            weights = {c: w for c, w in weights.items() if c not in EQUITY_CLASSES}
        wsum = sum(weights.values())
        safe_w = {c: w for c, w in weights.items() if c in (IG_BOND, CASH)}
        safe_budget = budget * sum(safe_w.values()) / wsum if wsum else 0.0
        sb, n = allocate_buys(safe_budget, safe_w, instruments, day, reason + "(B-2 안전자산)")
        buys += sb
        notes += n
        dust = sum(o.amount for o in buys if o.asset_class == CASH)
        buys = [o for o in buys if o.asset_class != CASH]
        hold = budget - safe_budget + dust
        if hold > 0.5:
            buys.append(Order("매수", ticker, name, CASH, hold, 1.0, day,
                              "현금성 배분·B-2 위험자산 매수 중단분·자투리 → CMA"))
    else:
        buys, n = allocate_buys(budget, weights, instruments, day, reason)
        notes += n
    return buys, notes, withdrawn, max(0.0, cash_need - withdrawn)


def _rotation_kwargs(equity_rotation: bool, sells: list, gaps: dict, total: float) -> dict:
    if not equity_rotation:
        return {}
    return dict(equity_budget=sum(o.amount for o in sells if o.asset_class in EQUITY_CLASSES),
                equity_deficits={c: total * -g / 100 for c, g in gaps.items()
                                 if c in EQUITY_CLASSES and g < 0})


def dilution_outlook(portfolio: Portfolio, st: SoftMigrationState, free_cash: float) -> list:
    """유예 자산 때문에 남는 비중 초과를 잉여 현금만으로 ±3%p까지 희석하는 데 걸리는 기간"""
    out = []
    total = portfolio.total()
    cv = portfolio.class_values()
    adj = locked_adjusted_targets(portfolio, st.targets)
    classes = {portfolio.find(t).asset_class for t in st.deferred if portfolio.find(t)}
    for c in classes:
        gap = cv[c] / total * 100 - adj[c] if total else 0
        if gap <= SOFT_THRESHOLD:
            continue
        needed_total = cv[c] / ((adj[c] + SOFT_THRESHOLD) / 100)
        extra = needed_total - total
        if free_cash > 0:
            out.append(f"{c} 비중 초과 {gap:+.1f}%p: 잉여 현금만으로 ±{SOFT_THRESHOLD:.0f}%p까지 희석하려면 "
                       f"약 {won(extra)} (월 {won(free_cash)} 기준 약 {math.ceil(extra / free_cash)}개월)")
        else:
            out.append(f"{c} 비중 초과 {gap:+.1f}%p: 잉여 현금이 없어 희석 불가 → 유예 자산 회복 대기")
    return out


def soft_migration_initial_plan(portfolio: Portfolio, st: SoftMigrationState, instruments: dict, *,
                                hold_buys: bool = False, safe_only: bool = False,
                                cash_need: float = 0.0, equity_rotation: bool = False,
                                sell_deadline_days: Optional[int] = None) -> SoftPlan:
    """
    Step 2: 1차 매매
    - 비중 초과 + 수익 자산 → 수익률 높은 순으로 매도 (해외주식은 비과세 여유 안에서)
    - 비중 초과 + 손실 자산 → 매도 유예, 향후 가계부 잉여 현금으로 비중 희석
    - 매도 대금 → 비중 미달 자산 매수 (트리거 발생 시 STAGE 4 규칙 적용)
    """
    adj = locked_adjusted_targets(portfolio, st.targets)
    total = portfolio.total()
    gaps = portfolio.gaps(adj)
    sells, notes = [], []
    room = st.tax_room
    net = 0.0

    for t, why in st.deferred.items():
        h = portfolio.find(t)
        if h:
            notes.append(f"{h.name}: {h.asset_class} 비중 초과지만 {why} → 매도 유예, 가계부 잉여 현금으로 희석")

    for c, g in gaps.items():
        if g <= 0 or c == CASH:
            continue
        excess = total * g / 100
        cands = sorted([h for h in portfolio.holdings if h.asset_class == c and h.profit_pct >= 0
                        and settles_in_time(h, sell_deadline_days)
                        and h.ticker not in st.deferred and h.ticker not in st.locked],
                       key=lambda h: -h.profit_pct)
        for h in cands:
            if excess <= 0:
                break
            want = min(excess, h.value)
            amt = _tax_limited_amount(h, want, room)
            if amt < want:
                notes.append(f"{h.name}: 해외주식 비과세 여유(손익 상계 반영)로 매도 {won(amt)}까지 제한")
            o = _sell_order(h, amt, 0, "전략B 초과·수익 자산 매도", round_up=False,
                            purpose=_plan_sell_purpose(cash_need, safe_only))
            if o:
                sells.append(o)
                excess -= o.amount
                g_ = _overseas_gain(h, o.amount)
                net += g_
                room = max(0.0, room - g_)

    # 목표를 넘는 현금성 자산도 매수 재원으로
    cash_excess = max(0.0, total * gaps[CASH] / 100)
    for h in portfolio.holdings:
        if cash_excess <= 0:
            break
        if h.asset_class == CASH and not h.locked:
            o = _sell_order(h, min(cash_excess, h.value), 0, "초과 현금 투입", round_up=False,
                            purpose=_plan_sell_purpose(cash_need, safe_only))
            if o:
                sells.append(o)
                cash_excess -= o.amount

    settle = max((portfolio.find(o.ticker).settlement_days for o in sells), default=0)
    under = {c: -g for c, g in gaps.items() if g < 0}
    buys, n, withdrawn, uncovered = _route_proceeds(
        sum(o.amount for o in sells), under, instruments, settle,
        hold_buys=hold_buys, safe_only=safe_only, cash_need=cash_need, reason="전략B 미달 자산 매수",
        purpose=_plan_sell_purpose(cash_need, safe_only),
        **_rotation_kwargs(equity_rotation, sells, gaps, total))
    return SoftPlan(sells, buys, notes + n, withdrawn, uncovered, net, is_initial=True)


def soft_migration_dilution_step(portfolio: Portfolio, st: SoftMigrationState, free_cash: float,
                                 instruments: dict, *, hold_buys: bool = False, safe_only: bool = False,
                                 cash_need: float = 0.0, equity_rotation: bool = False,
                                 sell_deadline_days: Optional[int] = None) -> SoftPlan:
    """
    Step 3: 전환기 순환
    - 희석으로 비중 초과가 해소된 유예 자산 → 유예 해제(보유 유지)
    - 유예 자산 회복 시 단계적 매도: -5% 이내 20%, 본전 이상 50% (자산군 초과분 한도)
    - 가계부 잉여 현금 + 단계적 매도 대금 → 비중 미달 자산 희석 매수
    - B-2 적용 중: 비중 초과가 된 수익권 위험 자산을 초과분의 50%씩 매도 → 채권·현금성 교체
    - 트리거 발생 시: 잉여 현금 투입 중단, 매도 대금은 부족 현금 우선 (STAGE 4 규칙)
    """
    adj = locked_adjusted_targets(portfolio, st.targets)
    total = portfolio.total()
    gaps = portfolio.gaps(adj)
    notes, sells = [], []
    room = st.tax_room
    net = 0.0

    for t in list(st.deferred):
        h = portfolio.find(t)
        if h is None:
            st.deferred.pop(t)
        elif gaps[h.asset_class] <= 0:
            st.deferred.pop(t)
            notes.append(f"{h.name}: 희석으로 {h.asset_class} 비중 초과 해소 → 유예 해제(보유 유지)")

    excess_left = {c: total * g / 100 for c, g in gaps.items() if g > 0}
    for t in list(st.deferred):
        h = portfolio.find(t)
        frac = next((f for lim, f in GRADUAL_EXIT_RULES if h.profit_pct >= lim), None)
        if frac is None or not settles_in_time(h, sell_deadline_days):
            continue
        want = min(h.value * frac, excess_left.get(h.asset_class, 0.0))
        amt = _tax_limited_amount(h, want, room)
        o = _sell_order(h, amt, 0, f"유예 자산 단계적 매도 {int(frac * 100)}% (수익률 {h.profit_pct:.1f}%)",
                        purpose=_plan_sell_purpose(cash_need, safe_only),
                        round_up=True)
        if o:
            sells.append(o)
            excess_left[h.asset_class] -= o.amount
            g_ = _overseas_gain(h, o.amount)
            net += g_
            room = max(0.0, room - g_)

    # B-2: 새로 비중 초과가 된 수익권 위험 자산 → 단계적으로 안전 자산 교체
    if safe_only:
        b2_sells, b2_notes, b2_net = b2_gradual_exit(
            portfolio.apply(sells), st.targets, exclude=set(st.deferred) | st.locked, tax_room=room)
        sells += b2_sells
        notes += b2_notes
        net += b2_net
        room = max(0.0, room - b2_net)

    # 목표를 넘는 현금성 자산(트리거 때 대기시킨 현금 등): 부족 현금 충당 → 해제 후 재투입
    cash_excess = max(0.0, total * gaps[CASH] / 100)
    use_cash = min(cash_excess, cash_need) if hold_buys else cash_excess
    for h in portfolio.holdings:
        if use_cash <= 0.5:
            break
        if h.asset_class == CASH and not h.locked:
            why = "대기 현금 → 부족 현금 충당" if hold_buys else "대기 현금 재투입"
            o = _sell_order(h, min(use_cash, h.value), 0, why, round_up=False,
                            purpose=PURPOSE_LIQUIDITY if cash_need > 0 else PURPOSE_FUNDING)
            if o:
                sells.append(o)
                use_cash -= o.amount

    budget = sum(o.amount for o in sells)
    if not hold_buys and free_cash > 0:
        budget += free_cash
        notes.append(f"가계부 잉여금 {won(free_cash)} → 비중 미달 자산 희석 매수")
    settle = max((portfolio.find(o.ticker).settlement_days for o in sells), default=0)
    under = {c: -g for c, g in gaps.items() if g < 0}
    buys, n, withdrawn, uncovered = _route_proceeds(
        budget, under, instruments, settle,
        hold_buys=hold_buys, safe_only=safe_only, cash_need=cash_need, reason="희석 매수",
        purpose=_plan_sell_purpose(cash_need, safe_only),
        **_rotation_kwargs(equity_rotation, sells, gaps, total))
    return SoftPlan(sells, buys, notes + n, withdrawn, uncovered, net)


def soft_migration_completed(portfolio: Portfolio, st: SoftMigrationState) -> bool:
    """Step 4: 유예 자산 전부 정리(또는 해제) AND 전 자산 |Gap| ≤ 3%p"""
    remaining = [t for t in st.deferred if portfolio.find(t)]
    adj = locked_adjusted_targets(portfolio, st.targets)
    ok_gap = all(abs(g) <= SOFT_THRESHOLD for g in portfolio.gaps(adj).values())
    return not remaining and ok_gap


# ── 전환 완료 3중 검증 + 180일 Time-out ────────────────────────────
class Trigger(Enum):
    A = "비상금 침범"
    B = "재무 잉여율 위기"
    C = "단기 목돈 지출"


class DataLink(Enum):
    """
    조건 3. 금융 데이터 연동 방식
    - MYDATA: 가계부(거래 내역·잔고)와 보유 종목 모두 자동 수집
    - MANUAL: 가계부 4대 항목은 직접 입력, 보유 종목은 증권사 API로 자동 수집
    """
    MYDATA = "마이데이터 자동 연동"
    MANUAL = "가계부 직접 입력 (필수 항목 연동 승인)"
    NONE = "미연동"


def _as_data_link(link) -> DataLink:
    if isinstance(link, DataLink):
        return link
    return DataLink.MYDATA if link else DataLink.NONE     # 이전 bool 인자 호환


# ── 가계부 미입력 알림 (직접 입력 사용자) ──────────────────────────
LEDGER_DUE_DAY = 5              # 매월 5일까지 지난달 가계부 입력
LEDGER_PRE_REMINDER_DAYS = 3    # 마감 3일 전부터 사전 알림
LEDGER_FREEZE_MONTHS = 2        # 연속 미입력 N개월(마감 경과 기준) → 신규 매수 중단


@dataclass
class Notification:
    level: str          # "사전 알림" / "미입력 알림" / "경고"
    title: str
    message: str
    period: str         # 대상 월 YYYY-MM
    created: date

    def __str__(self) -> str:
        return f"🔔 [{self.level}] {self.title}\n     {self.message}"


def _period_index(period: str) -> int:
    y, m = map(int, period.split("-"))
    return y * 12 + (m - 1)


def _index_period(idx: int) -> str:
    return f"{idx // 12}-{idx % 12 + 1:02d}"


def ledger_status(last_period: Optional[str], today: date) -> tuple:
    """(이번 마감 대상 월 index, 마감 경과 여부, 연속 미입력 개월 수)"""
    due_idx = today.year * 12 + (today.month - 1) - 1
    last_idx = _period_index(last_period) if last_period else None
    if last_idx is not None and last_idx >= due_idx:
        return due_idx, today.day > LEDGER_DUE_DAY, 0
    missed = due_idx - last_idx if last_idx is not None else 1
    return due_idx, today.day > LEDGER_DUE_DAY, missed


def ledger_reminders(data_link, last_period: Optional[str], today: date, sent: set) -> list:
    """
    직접 입력 사용자의 가계부 미입력 알림
    - 기준: 매월 LEDGER_DUE_DAY일까지 지난달 가계부(4대 필수 항목) 입력
    - 사전 알림: 마감 3일 전부터 마감일까지, 지난달 가계부가 없으면 1회
    - 미입력 알림: 마감이 지났는데 입력이 없으면 1회
    - 경고: 2개월 이상 연속 미입력 → 트리거 감시 중단 상태 경고 (월 1회)
    마이데이터 연동 사용자는 자동 수집되므로 알림 없음. 같은 알림은 중복 발송하지 않음(sent).
    """
    if _as_data_link(data_link) != DataLink.MANUAL:
        return []
    due_idx = today.year * 12 + (today.month - 1) - 1          # 이번 달 마감 대상 = 지난달
    target = _index_period(due_idx)
    last_idx = _period_index(last_period) if last_period else None
    if last_idx is not None and last_idx >= due_idx:
        return []
    items = "월 확정 수입 · 필수 고정 지출 · 비상금 계좌 입출금액/잔액 · 30일 내 목돈 지출"
    out = []
    if today.day <= LEDGER_DUE_DAY:
        if today.day >= LEDGER_DUE_DAY - LEDGER_PRE_REMINDER_DAYS and ("pre", target) not in sent:
            d = LEDGER_DUE_DAY - today.day
            out.append(Notification("사전 알림", f"{target} 가계부 입력 마감 D-{d}",
                                    f"{today.month}월 {LEDGER_DUE_DAY}일까지 {items}을 입력해 주세요.",
                                    target, today))
            sent.add(("pre", target))
        return out
    missed = due_idx - last_idx if last_idx is not None else 1
    if missed >= 2:
        if ("warn", target) not in sent:
            first = _index_period(last_idx + 1) if last_idx is not None else target
            out.append(Notification(
                "경고", f"가계부 {missed}개월 연속 미입력 ({first} ~ {target})",
                "비상금 침범·잉여율 위기·목돈 지출 트리거를 감지할 수 없어 신규 매수를 중단했습니다. "
                f"{target} 가계부까지 입력하면 매수가 재개됩니다. {items}을 바로 입력해 주세요.",
                target, today))
            sent.add(("warn", target))
    elif ("miss", target) not in sent:
        out.append(Notification(
            "미입력 알림", f"{target} 가계부가 입력되지 않았습니다",
            f"마감({today.month}월 {LEDGER_DUE_DAY}일)이 지났습니다. 입력 전까지 이번 달 트리거 감시와 "
            f"매수 금액 계산이 지연됩니다. {items}을 입력해 주세요.", target, today))
        sent.add(("miss", target))
    return out


def data_link_ready(link) -> bool:
    """마이데이터 연동 또는 가계부 직접 입력 승인이면 월간 현금 흐름 스캔 가능"""
    return _as_data_link(link) in (DataLink.MYDATA, DataLink.MANUAL)


def transition_ready(portfolio: Portfolio, targets: dict, strategy: str,
                     active_triggers: set, data_link, days_elapsed: int) -> tuple:
    """
    전환 완료 3중 검증 (AND) + 180일 Time-out
      조건 1: 비중 오차 (전략 A ±1%p / 전략 B ±3%p)
      조건 2: Trigger A·B·C 전면 해제
      조건 3: 금융 데이터 연동 — 마이데이터 자동 연동 또는 가계부 직접 입력 승인
    """
    threshold = 1.0 if strategy == "A" else 3.0
    c1 = all(abs(g) <= threshold for g in portfolio.gaps(targets).values())
    c2 = not active_triggers
    c3 = data_link_ready(data_link)
    if c1 and c2 and c3:
        return True, "3중 검증 통과 → 정식 관리 모드 전환"
    if days_elapsed >= TRANSITION_TIMEOUT_DAYS:
        if Trigger.A in active_triggers or Trigger.C in active_triggers:
            return False, "180일 경과했으나 Trigger A/C 활성 → 위기 해제 후 전환"
        return True, "180일 Time-out → 현재 비중을 임시 안정 상태로 수용, 정식 모드 강제 전환"
    reasons = []
    if not c1: reasons.append(f"비중 오차 ±{threshold}%p 미달")
    if not c2: reasons.append("특수 상황 트리거 활성")
    if not c3: reasons.append("금융 데이터 연동 미완료 (마이데이터 연동 또는 가계부 직접 입력 승인 필요)")
    return False, " / ".join(reasons)


def buildup_transition_ready(rounds_done: bool, active_triggers: set, data_link) -> tuple:
    """
    경로 A 구축 완료 판정 (AND)
      조건 1: 3회 분할 매수 완료
      조건 2: Trigger A·B·C 전면 해제
      조건 3: 금융 데이터 연동 — 마이데이터 자동 연동 또는 가계부 직접 입력 승인
    """
    c2 = not active_triggers
    c3 = data_link_ready(data_link)
    if rounds_done and c2 and c3:
        return True, f"구축 완료 검증 통과 ({_as_data_link(data_link).value}) → 정식 관리 모드 전환"
    reasons = []
    if not rounds_done: reasons.append("분할 매수 진행 중")
    if not c2: reasons.append("특수 상황 트리거 활성 → 해제 후 전환")
    if not c3: reasons.append("금융 데이터 연동 미완료 (마이데이터 연동 또는 가계부 직접 입력 승인 필요)")
    return False, " / ".join(reasons)


# ════════════════════════════════════════════════════════════════════
# STAGE 4. 트리거 감지
# ════════════════════════════════════════════════════════════════════
@dataclass
class LedgerSnapshot:
    """
    월간 가계부 입력 (전환기 필수 4대 항목)
      ① monthly_income          : 월 확정 수입 = 이번 달 들어온 정기 수입 실수령액
                                  (마이데이터·직접 입력 공통 기준, 평균값 사용 안 함)
      ② essential_expense       : 필수 고정 지출 (주거비·대출 원리금·공과금·보험료 등)
      ③ 비상금 계좌 입출금액     : emergency_deposit(입금), emergency_withdrawal(출금)
         + emergency_balance    : 비상금 계좌 잔액
           (비워 두면 '지난달 잔액 + 입금 − 출금'으로 자동 계산)
      ④ upcoming_cf, dday       : 30일(달력) 이내 목돈 지출 금액과 남은 일수(D-Day, 달력 기준)
         bdays                  : 지출일까지 남은 한국 영업일 수 (정산 판단·화면 표시용)
                                  due_date(지출일)·as_of(판단일)가 있으면 정산 가능 여부를 휴장일까지 반영
    Trigger A·C 는 '비상금 계좌 잔액'으로 판단합니다.
    시스템이 Trigger A 대응으로 비상금 계좌에 이체한 금액(매도 대금·투자 대기 현금·잉여금)은
    다음 달 잔액에 자동 반영되므로, 입금액에는 사용자가 직접 넣은 돈만 입력합니다.
    """
    monthly_income: float
    essential_expense: float
    emergency_balance: Optional[float] = None
    emergency_deposit: float = 0.0
    emergency_withdrawal: float = 0.0
    upcoming_cf: float = 0.0
    dday: Optional[int] = None
    system_transfer: float = 0.0     # 지난달 시스템이 비상금 계좌로 이체한 금액 (자동 반영, 입력 불필요)
    period: Optional[str] = None     # 가계부 대상 월 "YYYY-MM" (직접 입력 사용자 미입력 알림용)
    balance_source: str = ""         # 잔액 출처: "마이데이터 연동 잔액" / "직접 입력" / ""(자동 계산)
    expense_reserved: float = 0.0    # Trigger C로 이미 현금화해 둔 지출 대기 현금 (시스템 관리)
    total_expense: float = 0.0       # 월 지출 합계(필수 + 비필수). 0이면 필수 지출로 대신 계산
    irregular_income: float = 0.0    # 비정기 수입 (등급·Buffer·트리거 판단 제외, 사용 순서에 따라 배분)
    irregular_taxable: float = 0.0   # 그중 사업·용역 소득 (종합소득세 대비 몫 적립 대상)
    bdays: Optional[int] = None      # 지출일까지 남은 한국 영업일 수 (휴장일 제외)
    due_date: Optional[date] = None  # 가장 가까운 목돈 지출일
    as_of: Optional[date] = None     # 판단 기준일 (매도 주문일)

    def deadline(self) -> Optional["SettleDeadline"]:
        """매도 정산 마감: 영업일 수 + 지출일 (Trigger C 매도 후보 거르기는 휴장일을 반영한 날짜로 판단)"""
        if self.dday is None:
            return None
        return SettleDeadline(self.bdays if self.bdays is not None else self.dday, self.due_date, self.as_of)

    def dday_label(self) -> str:
        if self.dday is None:
            return ""
        return f"D-{self.dday}" + (f" · 영업일 {self.bdays}일" if self.bdays is not None else "") + \
            (f" · {_md(self.due_date)}" if self.due_date else "")

    @property
    def c_current(self) -> float:
        """알고리즘의 C_current = 비상금 계좌 잔액"""
        if self.emergency_balance is None:
            raise ValueError("비상금 계좌 잔액이 계산되지 않았습니다. 첫 달은 잔액을 입력해 주세요.")
        return self.emergency_balance

    @c_current.setter
    def c_current(self, value: float) -> None:
        self.emergency_balance = value

    @property
    def emergency_net_flow(self) -> float:
        return self.emergency_deposit - self.emergency_withdrawal

    @property
    def monthly_expenses(self) -> float:
        """월 지출 합계 (가계부 전체 지출). 입력이 없으면 필수 지출로 대신"""
        return max(self.total_expense, self.essential_expense)

    @property
    def free_cash(self) -> float:
        """이번 달 순잉여금 Free_Cash = Monthly_Income − Monthly_Expenses (스마트 바이 재원)"""
        return self.monthly_income - self.monthly_expenses

    @property
    def buffer(self) -> float:
        """재무 잉여율은 등급 판단용이므로 필수 지출 기준 (STAGE 1·2 정의 유지)"""
        return calc_buffer(self.monthly_income, self.essential_expense)


LEDGER_INPUT_GUIDE = """[월간 가계부 입력 안내]
 ① 월 확정 수입       : 이번 달 정기적으로 들어온 실수령액
 ② 필수 고정 지출     : 주거비·대출 원리금·공과금·식비·보험료 등 줄이기 어려운 지출 합계
 ③ 비상금 계좌 입출금액: 이번 달 비상금 계좌에 넣은 돈(입금)과 뺀 돈(출금)
    · 비상금 계좌 잔액 : 입출금 후 비상금 계좌에 남아 있는 금액
      (투자 계좌·투자 대기 현금·생활비 통장은 포함하지 않습니다.
       비워 두면 지난달 잔액 + 입금 − 출금 + 시스템 이체액으로 자동 계산합니다. 첫 달은 꼭 입력해 주세요.)
    · 시스템 이체액    : 비상금 복구를 위해 시스템이 옮긴 돈은 자동 반영되니 입금액에 넣지 마세요.
 ④ 30일 이내 목돈 지출: 한 달 안에 나갈 큰 지출의 금액과 날짜"""


def detect_triggers(snap: LedgerSnapshot, c_reserve: float, buffer_old: float) -> set:
    t = set()
    if snap.c_current < c_reserve:
        t.add(Trigger.A)
    b = snap.buffer
    if b < 10 or (buffer_old > 0 and b <= buffer_old * 0.5):
        t.add(Trigger.B)
    if snap.dday is not None and 0 <= snap.dday <= C_WINDOW_DAYS and \
            snap.upcoming_cf > snap.c_current + snap.expense_reserved:
        t.add(Trigger.C)
    return t


# ── 트리거 해제 기준 (히스테리시스) + 최소 유지 기간 ─────────────────
# 진입 기준은 detect_triggers 그대로. 해제는 진입선보다 한 걸음 더 회복해야 하고,
# 최소 유지 기간을 채워야 해서 기준선 근처에서 켜졌다 꺼졌다 하는 반복을 막습니다.
A_RELEASE_RATIO = 1.05          # A 해제: 잔액 ≥ 필수 비상금의 105%
A_HOLD_DAYS = (7, 14, 30)       # A 해제 조건 연속 유지 일수 (재진입할 때마다 한 단계씩)
B1_RELEASE_BUFFER = 12.0        # B-1 해제: Buffer ≥ 12%
B2_ENTRY_RATIO = 0.50           # B-2 진입: Buffer ≤ 기준의 50%
B2_PARTIAL_RATIO = 0.60         # B-2 부분 회복: Buffer > 기준의 60%
B2_FULL_RATIO = 0.85            # B-2 완전 복귀: Buffer ≥ 기준의 85%
B_HOLD_MONTHS = (3, 6, 12)      # B-1·B-2 최소 유지 기간(월 마감 횟수, 재진입할 때마다 한 단계씩)
RELEASE_STREAK_MONTHS = 2       # B-2 해제 조건 연속 달 수 · 강한 회복 연속 달 수
C_RELEASE_RATIO = 1.05          # C 해제: 대비 현금 ≥ 지출액의 105% (또는 지출일 경과)
REENTRY_WINDOW_DAYS = 31        # 해제 후 이 기간 안에 같은 트리거가 다시 걸리면 재진입 단계 +1


@dataclass
class TriggerLatch:
    """트리거 하나의 진입·유지·해제 상태"""
    active: bool = False
    entered: Optional[date] = None
    months: int = 0                  # 진입 후 지난 월 마감 횟수 (B)
    streak: int = 0                  # 해제 조건 연속 달 수 (B)
    strong: int = 0                  # 강한 회복(기준의 85% 이상) 연속 달 수 (B)
    ok_since: Optional[date] = None  # 해제선 이상이 이어진 첫날 (A)
    level: int = 0                   # 재진입 단계 (0: 기본)
    released: Optional[date] = None  # 마지막 해제일


LATCH_LABELS = {"A": "Trigger A", "B1": "B-1", "B2": "B-2", "C": "Trigger C"}


def _sell_until(cands: list, need: float, reason: str) -> tuple:
    orders = []
    for h in cands:
        if need <= 0:
            break
        o = _sell_order(h, min(need, h.value), 0, reason, round_up=True,      # 유동성 매도는 즉시 발주
                        purpose=PURPOSE_LIQUIDITY)
        if o:
            orders.append(o)
            need -= o.amount
    return orders, max(0.0, need)


# ── Trigger A ──────────────────────────────────────────────────────
@dataclass
class TriggerAPlan:
    shortage: float
    mode: str
    orders: list
    uncovered: float
    note: str


def handle_trigger_a(snap: LedgerSnapshot, c_reserve: float, portfolio: Portfolio, targets: dict) -> TriggerAPlan:
    shortage = c_reserve - snap.c_current
    fc = snap.free_cash
    if fc > 0 and shortage <= 2 * fc:
        months = math.ceil(shortage / fc)
        return TriggerAPlan(shortage, "A-1 수입 충전 모드", [], 0.0,
                            f"신규 매수 동결, 유입 수입 100% 비상금 적립 (약 {months}개월 내 복구)")
    gaps = portfolio.gaps(targets)

    def key(h: Holding):
        cost = (h.estimate_tax(h.value) + h.estimate_fee(h.value)) / h.value if h.value else 0
        if h.profit_pct >= 0 and gaps[h.asset_class] > 0:
            return (0, -gaps[h.asset_class], 0)
        if h.profit_pct <= -10:
            return (2, -h.profit_pct, 0)  # 손실 작은 것부터, 최후 순위
        return (1, h.volatility, cost)

    cands = sorted([h for h in portfolio.holdings if not h.locked and h.asset_class != CASH], key=key)
    orders, left = _sell_until(cands, shortage, "Trigger A 긴급 현금화")
    return TriggerAPlan(shortage, "A-2 긴급 현금화 모드", orders, left,
                        "신규 매수 동결, 수익권·비중 초과 → 저변동/저비용 → 대손실 순 매도")


# ── Trigger B ──────────────────────────────────────────────────────
@dataclass
class TriggerBResult:
    kind: str
    new_tier: int
    targets: dict
    new_score: Optional[float] = None
    note: str = ""
    cash_floor: float = 0.0


def handle_trigger_b1(buffer_new: float, current_tier: int) -> TriggerBResult:
    """
    B-1 Hard Stop (Buffer < 10%)
    - 위험 자산 신규 매수 전면 동결
    - 현금성 자산 최우선 확보 포트폴리오로 목표 비중 하향 고정
        · Buffer 5~10% : B-1 Tier 2 = 주식 10% / 채권 40% / 대체 0% / 현금 50%
        · Buffer 5% 미만: B-1 Tier 1 = 주식 0%  / 채권 30% / 대체 0% / 현금 70%
      (원래 등급이 더 낮으면 더 낮은 B-1 등급 적용)
    """
    cap = 20 if buffer_new < 5 else 40
    tier = min(current_tier, score_to_tier(cap))
    model = B1_PORTFOLIOS[tier]
    return TriggerBResult("B-1 Hard Stop", tier, model.targets, None,
                          f"Cap_financial={cap}, 위험 자산 신규 매수 전면 동결, {model.name} "
                          f"(주식 {model.targets[FOR_EQ]:.0f}% / 채권 {model.targets[IG_BOND]:.0f}% / "
                          f"대체 0% / 현금 {model.targets[CASH]:.0f}%)로 목표 비중 하향 고정",
                          cash_floor=model.targets[CASH])


def handle_trigger_b2(base_score: float, buffer_new: float, buffer_old: float, current_tier: int) -> TriggerBResult:
    ratio = clamp(buffer_new / buffer_old, 0, 1) if buffer_old > 0 else 0
    new_score = base_score * (0.7 + 0.3 * ratio)
    mapped = score_to_tier(new_score)
    # 예외 A(최대 2단계 하향) + 예외 B(최소 1단계 하향)
    new_tier = max(1, max(current_tier - 2, min(current_tier - 1, mapped)))
    if current_tier == 2:
        model = TIER1_LIQUID
    elif current_tier == 1:
        model = TIER1_ULTRA_SAFE
    else:
        model = MODEL_PORTFOLIOS[new_tier]
    return TriggerBResult("B-2 Soft Adjust", new_tier, model.targets, new_score,
                          f"{model.name} 적용, 비상금 개월 수 +1, 주식 매수 중단·안전자산 희석")


def b2_quarterly_review(applied_tier: int, months_since: int, buffer_new: float, buffer_old: float) -> int:
    """3개월 모니터링 후 잉여율 미회복 시 1단계 추가 하향"""
    if months_since >= 3 and buffer_old > 0 and buffer_new < buffer_old * 0.5:
        return max(1, applied_tier - 1)
    return applied_tier


def b2_recovery(original_tier: int, applied_tier: int, base_score: float,
                buffer_new: float, buffer_old: float) -> tuple:
    ratio = buffer_new / buffer_old if buffer_old > 0 else 0
    if ratio >= 0.85:
        return original_tier, "Path 1 완전 정상 복귀"
    if ratio >= 0.5:
        rescore = base_score * (0.7 + 0.3 * ratio)
        tier = min(original_tier, max(applied_tier + 1, score_to_tier(rescore)))
        return tier, f"Path 2 부분 회복 (재계산 점수 {rescore:.1f})"
    return applied_tier, "미회복 → 현 등급 유지"


# ── Trigger C ──────────────────────────────────────────────────────
# 매도 점수 Score_i 의 모든 항은 % 단위(0~100 스케일)로 통일합니다.
#   Gap_i      : (자산군 현재 비중 − 목표 비중)        → 총자산 대비 %
#   Vol_i/(D+1): 연 변동성 % ÷ (D+1)                 → %
#   Profit_i   : 평가 수익률                          → 매수 원가 대비 %
#   LossPenal_i: α × |Profit_i| × 비중 계수(−1~1)     → %
#   CostPenal_i: β × (세금+수수료) ÷ 필요 현금 × 100   → 필요 현금 대비 %
LOSS_ALPHA = 1.5    # 원금 손실 방지 가중치 α
COST_BETA = 1.0     # 세금·수수료 가중치 β


def loss_ratio_factor(current_ratio: float, target_ratio: float) -> float:
    """
    손실 페널티의 비중 계수 (1 − 현재 비중 ÷ 목표 비중)
    - −1 ~ 1 범위로 제한 (비중 초과 쪽 가산점이 무한히 커지는 것 방지)
    - 목표 비중 0% → −1 (완전 초과로 간주, 최대 매도 유도)
    """
    if target_ratio <= 0:
        return -1.0
    return clamp(1 - current_ratio / target_ratio, -1.0, 1.0)


STOCK_TRANSACTION_TAX = 0.002     # 국내 개별 주식 매도 시 증권거래세(+농특세) 합계 0.20% (2026년~)
DOMESTIC_OTHER_ETF_TAX = 0.154    # 국내 상장 기타 ETF(해외지수·채권·원자재 등) 매매차익 배당소득세


def estimate_sell_tax(h: Holding, amount: float, realized_overseas_ytd: float = 0.0) -> float:
    """
    매도 세금 추정 (상품·계좌 유형별)
    - 현금성 자산, 절세 계좌(ISA·연금저축·IRP): 0원 (과세 이연·비과세)
    - 해외 상장 주식·ETF: 올해 실현 손익(손실 상계)에 이번 차익을 더해 250만 원 공제 초과분 × 22%
    - 국내 개별 주식(소액주주): 양도세 없음, 매도금액 × 증권거래세 0.20%
    - 국내 상장 주식형 ETF(국내주식 자산군): 매매차익 비과세
    - 국내 상장 기타 ETF(해외지수·채권·금 등): 매매차익 × 15.4%
    - 종목에 tax_rate 를 직접 지정하면 그 세율을 우선 사용
    """
    if h.asset_class == CASH or h.tax_advantaged or h.price <= 0:
        return 0.0
    gain = amount * (1 - h.avg_price / h.price)
    if h.overseas:
        before = max(0.0, realized_overseas_ytd - OVERSEAS_TAX_FREE_LIMIT)
        after = max(0.0, realized_overseas_ytd + gain - OVERSEAS_TAX_FREE_LIMIT)
        return max(0.0, after - before) * OVERSEAS_TAX_RATE
    if getattr(h, "product_type", "ETF") == "주식":
        return amount * STOCK_TRANSACTION_TAX
    if h.tax_rate > 0:
        return max(0.0, gain) * h.tax_rate
    if h.asset_class == DOM_EQ:
        return 0.0
    return max(0.0, gain) * DOMESTIC_OTHER_ETF_TAX


def cost_penalty(h: Holding, amount: float, realized_overseas_ytd: float = 0.0) -> float:
    """CostPenal_i = (예상 세금 + 수수료) ÷ 매도 금액 × 100 (%)"""
    if amount <= 0:
        return 0.0
    return (estimate_sell_tax(h, amount, realized_overseas_ytd) + h.estimate_fee(amount)) / amount * 100


def tax_aware_sell_key(h: Holding, amount: Optional[float] = None, ytd: float = 0.0) -> tuple:
    """리밸런싱 매도 순서: ① 절세·비과세 계좌 ② CostPenal_i 낮은 순(세금 부담 적은 자산부터)"""
    return (not h.tax_advantaged, cost_penalty(h, amount if amount else h.value, ytd))


@dataclass
class SellScore:
    holding: Holding
    score: float
    gap: float           # %
    vol_term: float      # %
    profit: float        # %
    loss_factor: float   # −1 ~ 1
    loss_pen: float      # %
    tax: float           # 원
    fee: float           # 원
    cost_pen: float      # %
    excluded: str = ""

    def row(self) -> str:
        sc = "제외" if self.score == -math.inf else f"{self.score:+.2f}%"
        return (f"{self.holding.name:<14} Score {sc:>8} | Gap {self.gap:+.1f}% | 변동성 −{self.vol_term:.2f}% | "
                f"수익률 {self.profit:+.1f}% | 손실P {self.loss_pen:+.2f}% (계수 {self.loss_factor:+.2f}) | "
                f"비용P {self.cost_pen:.2f}% (세금 {won(self.tax)}, 수수료 {won(self.fee)})"
                + (f" | {self.excluded}" if self.excluded else ""))


def trigger_c_scores(portfolio: Portfolio, targets: dict, required_cash: float, dday: int,
                     realized_overseas_ytd: float = 0.0, deadline=None) -> list:
    """
    Score_i = 0.6·Gap_i − Vol_i/(D+1) + 0.4·Profit_i − LossPenal_i − CostPenal_i   (모든 항 % 단위)
    LossPenal_i = α·|Profit_i|·clamp(1 − Current_i/Target_i, −1, 1)  (Profit_i < 0, 목표 0% → 계수 −1)
    CostPenal_i = β·(Tax_i + Fee_i) / Required_Cash × 100            (세금은 비과세 한도 반영)
    정산일 T+N > D 인 자산은 Score = −∞ (매도 제외)
      D 는 한국 영업일 기준 D-Day. deadline(지출일·주문일)이 있으면 주말·양국 휴장일을 반영한
      실제 현금화일이 지출일보다 늦은 자산을 제외
    """
    cur = portfolio.current_ratios()
    out = []
    for h in portfolio.holdings:
        if h.asset_class == CASH or h.locked:
            continue
        c = h.asset_class
        tgt = targets.get(c, 0.0)
        gap = cur[c] - tgt
        vol_term = h.volatility / (dday + 1)
        profit = h.profit_pct
        factor = loss_ratio_factor(cur[c], tgt)
        loss_pen = LOSS_ALPHA * abs(profit) * factor if profit < 0 else 0.0
        amt = min(h.value, required_cash)
        tax = estimate_sell_tax(h, amt, realized_overseas_ytd)
        fee = h.estimate_fee(amt)
        cost_pen = COST_BETA * (tax + fee) / required_cash * 100 if required_cash > 0 else 0.0
        score = 0.6 * gap - vol_term + 0.4 * profit - loss_pen - cost_pen
        excluded = ""
        due = getattr(deadline, "due", None)
        if due is not None and not settles_in_time(h, deadline):
            score, excluded = -math.inf, f"현금화 {_md(cash_date(h, deadline.trade_day or clock_today()))} > 지출일 {_md(due)}"
        elif due is None and not settles_in_time(h, deadline if deadline is not None else dday):
            limit = int(deadline) if deadline is not None else dday
            score, excluded = -math.inf, f"정산 T+{h.settlement_days} > 남은 영업일 {limit}일"
        out.append(SellScore(h, score, gap, vol_term, profit, factor if profit < 0 else 0.0,
                             loss_pen, tax, fee, cost_pen, excluded))
    return sorted(out, key=lambda s: s.score, reverse=True)


@dataclass
class TriggerCPlan:
    shortage: float
    scores: list
    orders: list
    uncovered: float

    def score_table(self) -> list:
        return ["  매도 점수표 (모든 항 % 단위, 높은 순 매도)"] + [f"    {s.row()}" for s in self.scores]


def handle_trigger_c(snap: LedgerSnapshot, portfolio: Portfolio, targets: dict,
                     realized_overseas_ytd: float = 0.0) -> TriggerCPlan:
    shortage = max(0.0, snap.upcoming_cf - snap.c_current - snap.expense_reserved)
    scores = trigger_c_scores(portfolio, targets, shortage, snap.dday or 0, realized_overseas_ytd,
                              snap.deadline())
    cands = [s.holding for s in scores if s.score != -math.inf]
    orders, left = _sell_until(cands, shortage, "Trigger C 타임라인 현금화")
    for o in orders:
        o.deadline_days = snap.deadline()
    return TriggerCPlan(shortage, scores, orders, left)


def trigger_c_release(c_current_after: float, c_reserve: float) -> str:
    if c_current_after >= c_reserve:
        return "NORMAL"      # 기존 리밸런싱/전환 모드 복귀
    return "TRIGGER_A"       # 연쇄 전환


# ════════════════════════════════════════════════════════════════════
# STAGE 4. 정식 관리 모드: 스마트 바이 + 밴드 리밸런싱
# ════════════════════════════════════════════════════════════════════
BUY_ACCOUNT_PRIORITY = ("ISA", "연금저축", "IRP", "일반")   # 매수 시 절세·비과세 계좌 우선


def assign_buy_accounts(instruments: dict, available: tuple) -> dict:
    """
    자산군별 매수 종목의 매수 계좌 지정: 보유한 계좌 중 절세 계좌 우선
    - 해외 상장 상품: 일반(해외주식) 계좌만 가능
    - 현금성 이체(CMA): 계좌 지정 없음
    ※ IRP 위험자산 70% 한도·연간 납입 한도는 계좌별 잔여 한도 데이터 연동 시 추가 확인 필요
    """
    out = {}
    for cls, inst in instruments.items():
        n = copy.copy(inst)
        if cls != CASH:
            if inst.overseas:
                n.account = "일반"
            else:
                n.account = next((a for a in BUY_ACCOUNT_PRIORITY if a in available), "일반")
        out[cls] = n
    return out


# ── 계좌별 잔여 한도 연동 ─────────────────────────────────────────
PENSION_GROUP_ANNUAL_LIMIT = 18_000_000     # 연금저축 + IRP 합산 연간 납입 한도
IRP_RISKY_CAP = 0.70                         # IRP 위험자산 편입 한도
RISKY_FOR_PENSION = {DOM_EQ, FOR_EQ, HY_BOND, COMMODITY, CRYPTO}   # 연금 계좌 위험자산으로 보는 자산군
# 기본값(2026년 기준 예시) — 실제로는 증권사·마이데이터 조회값으로 덮어씀
DEFAULT_ACCOUNT_LIMITS = {
    "ISA": dict(annual_limit=20_000_000, total_limit=100_000_000, tax_free_limit=2_000_000),
    "연금저축": dict(annual_limit=PENSION_GROUP_ANNUAL_LIMIT),
    "IRP": dict(annual_limit=PENSION_GROUP_ANNUAL_LIMIT, risky_cap_ratio=IRP_RISKY_CAP),
}


@dataclass
class AccountLimit:
    """계좌별 잔여 한도 (증권사·마이데이터 조회값)"""
    account: str
    annual_limit: float
    contributed_ytd: float = 0.0              # 올해 납입액
    total_limit: Optional[float] = None       # ISA 총 납입 한도
    total_contributed: float = 0.0
    tax_free_limit: Optional[float] = None    # ISA 비과세 한도
    tax_free_used: float = 0.0                # ISA 누적 순이익(비과세 한도 사용분)
    risky_cap_ratio: Optional[float] = None   # IRP 위험자산 한도
    account_value: float = 0.0
    risky_value: float = 0.0

    @property
    def remaining_contribution(self) -> float:
        rem = self.annual_limit - self.contributed_ytd
        if self.total_limit is not None:
            rem = min(rem, self.total_limit - self.total_contributed)
        return max(0.0, rem)

    def remaining_risky_room(self) -> float:
        """새로 넣는 돈 x를 전부 위험자산으로 살 때 (위험+x) ≤ 한도×(평가액+x) 를 만족하는 최대 x"""
        if self.risky_cap_ratio is None:
            return math.inf
        cap = self.risky_cap_ratio
        return max(0.0, (cap * self.account_value - self.risky_value) / (1 - cap))

    def summary(self) -> str:
        parts = [f"올해 납입 여력 {won(self.remaining_contribution)} (한도 {won(self.annual_limit)} 중 {won(self.contributed_ytd)} 사용)"]
        if self.total_limit is not None:
            parts.append(f"총 한도 잔여 {won(self.total_limit - self.total_contributed)}")
        if self.tax_free_limit is not None:
            parts.append(f"비과세 한도 잔여 {won(max(0.0, self.tax_free_limit - self.tax_free_used))}")
        if self.risky_cap_ratio is not None:
            ratio = self.risky_value / self.account_value * 100 if self.account_value else 0.0
            parts.append(f"위험자산 {ratio:.0f}% / 한도 {self.risky_cap_ratio * 100:.0f}% "
                         f"(추가 위험자산 여력 {won(self.remaining_risky_room())})")
        return f"{self.account}: " + ", ".join(parts)


class AccountLimitAPI:
    """계좌별 납입액·평가액 조회 인터페이스 (증권사 Open API·마이데이터로 구현)"""
    def fetch_limits(self) -> dict:
        raise NotImplementedError


class MockAccountLimitAPI(AccountLimitAPI):
    def __init__(self, data: dict):
        self.data = data

    def fetch_limits(self) -> dict:
        out = {}
        for acct, vals in self.data.items():
            base = dict(DEFAULT_ACCOUNT_LIMITS.get(acct, {"annual_limit": math.inf}))
            base.update(vals)
            out[acct] = AccountLimit(acct, **base)
        return out


def route_buys_by_limits(orders: list, limits: dict, priority: tuple = BUY_ACCOUNT_PRIORITY) -> tuple:
    """
    신규 자금 매수 주문을 계좌별 잔여 한도에 맞춰 나눔 (절세 계좌 우선)
    - ISA: 올해 납입 여력·총 한도 안에서
    - 연금저축·IRP: 두 계좌 합산 연 1,800만 원 안에서, 해외 상장 상품 불가
    - IRP: 위험자산(주식·원자재·고위험채 등)은 위험자산 70% 한도 여력 안에서
    - 남는 금액·해외 상장 상품은 일반 계좌로
    반환: (계좌가 지정된 주문, 안내)
    """
    notes = []
    pension_used = sum(l.contributed_ytd for a, l in limits.items() if a in ("연금저축", "IRP"))
    pension_room = max(0.0, PENSION_GROUP_ANNUAL_LIMIT - pension_used)
    room = {a: l.remaining_contribution for a, l in limits.items()}
    risky_room = {a: l.remaining_risky_room() for a, l in limits.items()}
    out = []
    for o in orders:
        if o.side != "매수" or o.asset_class == CASH or o.account == "일반":
            out.append(o)                       # 현금 이체·해외 상장 상품(일반 계좌 전용)은 그대로
            continue
        qty_left = o.quantity
        for acct in priority:
            if qty_left <= 0 or acct == "일반" or acct not in limits:
                continue
            avail = room[acct]
            if acct in ("연금저축", "IRP"):
                avail = min(avail, pension_room)
            if acct == "IRP" and o.asset_class in RISKY_FOR_PENSION:
                avail = min(avail, risky_room[acct])
            q = math.floor(min(avail, qty_left * o.price) / o.price)
            if q <= 0:
                continue
            n = copy.copy(o)
            n.quantity, n.account = q, acct
            out.append(n)
            spent = q * o.price
            room[acct] -= spent
            if acct in ("연금저축", "IRP"):
                pension_room -= spent
            if acct == "IRP" and o.asset_class in RISKY_FOR_PENSION:
                risky_room[acct] -= spent
            qty_left -= q
        if qty_left > 0:
            n = copy.copy(o)
            n.quantity, n.account = qty_left, "일반"
            out.append(n)
            if any(a in limits for a in priority if a != "일반"):
                notes.append(f"{o.name}: 절세 계좌 잔여 한도 부족 → {qty_left:,.4g}주 일반 계좌 매수")
    for a in limits:
        if room[a] < limits[a].remaining_contribution:
            notes.append(f"{a} 납입 예정 {won(limits[a].remaining_contribution - room[a])} "
                         f"(잔여 여력 {won(max(0.0, room[a]))})")
    return out, notes


# ── 달력 연동: 공휴일·명절(연도별 자동) + 재정 일정 + 사용자 지출 이벤트 ─────────
@dataclass
class CalendarEvent:
    day: date
    name: str
    kind: str                 # "공휴일" / "명절" / "대체공휴일" / "재정 일정" / "사용자 지출"
    amount: float = 0.0       # 사용자 지출 예정 금액
    big: bool = False         # 목돈 지출(Trigger C 감시 대상)


class HolidayProvider:
    """연도별 공휴일·명절 조회 인터페이스"""
    source = ""

    def fetch(self, year: int) -> list:
        raise NotImplementedError


def _holiday_kind(name: str) -> str:
    if "대체" in name:
        return "대체공휴일"
    if "설" in name or "추석" in name:
        return "명절"
    return "공휴일"


class DataGoKrHolidayAPI(HolidayProvider):
    """
    공공데이터포털 '한국천문연구원 특일 정보' API (우주항공청 월력요항 기준)
    getRestDeInfo 로 월별 공휴일(설·추석·대체공휴일·임시공휴일 포함)을 조회
    service_key: 공공데이터포털에서 발급받은 인증키
    """
    source = "공공데이터포털 특일 정보 API"
    URL = "https://apis.data.go.kr/B090041/openapi/service/SpcdeInfoService/getRestDeInfo"

    def __init__(self, service_key: str, timeout: float = 5.0):
        self.key, self.timeout = service_key, timeout

    def fetch(self, year: int) -> list:
        import json
        import urllib.parse
        import urllib.request
        events = []
        for month in range(1, 13):
            q = urllib.parse.urlencode({"serviceKey": self.key, "solYear": year, "solMonth": f"{month:02d}",
                                        "_type": "json", "numOfRows": 50})
            with urllib.request.urlopen(f"{self.URL}?{q}", timeout=self.timeout) as r:
                body = json.loads(r.read().decode())
            items = (((body.get("response") or {}).get("body") or {}).get("items") or {})
            items = items.get("item", []) if isinstance(items, dict) else []
            for it in ([items] if isinstance(items, dict) else items):
                if it.get("isHoliday") == "Y":
                    d = str(it["locdate"])
                    events.append(CalendarEvent(date(int(d[:4]), int(d[4:6]), int(d[6:])),
                                                it["dateName"], _holiday_kind(it["dateName"])))
        return events


class BuiltinHolidayTable(HolidayProvider):
    """
    API 장애 시 예비 데이터: 날짜가 고정된 공휴일 + 월력요항으로 확인한 설·추석·부처님오신날
    + 대체공휴일 규칙 계산 + 이미 지정된 선거일·임시공휴일
    (새로 지정되는 임시공휴일·선거일은 API로 반영)
    """
    source = "내장 예비 데이터"
    FIXED = [(1, 1, "신정"), (3, 1, "삼일절"), (5, 1, "노동절"), (5, 5, "어린이날"), (6, 6, "현충일"),
             (7, 17, "제헌절"), (8, 15, "광복절"), (10, 3, "개천절"), (10, 9, "한글날"), (12, 25, "성탄절")]
    FIXED_SINCE = {"노동절": 2026, "제헌절": 2026}          # 2026년부터 관공서 공휴일
    LUNAR = {
        2025: [("설날", [(1, 28), (1, 29), (1, 30)]), ("추석", [(10, 5), (10, 6), (10, 7)]),
               ("대체공휴일(추석)", [(10, 8)])],
        2026: [("설날", [(2, 16), (2, 17), (2, 18)]), ("추석", [(9, 24), (9, 25), (9, 26)])],
        2027: [("설날", [(2, 6), (2, 7), (2, 8)]), ("대체공휴일(설날)", [(2, 9)]),
               ("추석", [(9, 14), (9, 15), (9, 16)])],
        2028: [("설날", [(1, 25), (1, 26), (1, 27)]), ("추석", [(10, 2), (10, 3), (10, 4)]),
               ("대체공휴일(추석)", [(10, 5)])],
    }
    BUDDHA = {2025: (5, 5), 2026: (5, 24), 2027: (5, 13), 2028: (5, 2)}     # 부처님오신날 (음력 4월 8일)
    SPECIAL = {                                                             # 선거일·임시공휴일
        2025: [(1, 27, "임시공휴일"), (6, 3, "제21대 대통령 선거")],
        2026: [(6, 3, "제9회 전국동시지방선거")],
    }
    # 토·일요일과 겹치면 대체공휴일 (어린이날은 다른 공휴일과 겹쳐도)
    SUBSTITUTE_WEEKEND = {"삼일절", "광복절", "개천절", "한글날", "부처님오신날", "성탄절", "어린이날"}

    def fetch(self, year: int) -> list:
        ev = [CalendarEvent(date(year, m, d), n, "공휴일") for m, d, n in self.FIXED
              if year >= self.FIXED_SINCE.get(n, 0)]
        if year in self.BUDDHA:
            ev.append(CalendarEvent(date(year, *self.BUDDHA[year]), "부처님오신날", "공휴일"))
        for name, days in self.LUNAR.get(year, []):
            ev += [CalendarEvent(date(year, m, d), name, _holiday_kind(name)) for m, d in days]
        ev += [CalendarEvent(date(year, m, d), n, "공휴일") for m, d, n in self.SPECIAL.get(year, [])]
        return ev + self._substitutes(ev)

    def _substitutes(self, ev: list) -> list:
        """대체공휴일 계산 (설·추석 대체공휴일은 LUNAR 표에 직접 기록)"""
        taken = {e.day for e in ev}
        count = {}
        for e in ev:
            count[e.day] = count.get(e.day, 0) + 1
        out = []
        for e in sorted(ev, key=lambda x: x.day):
            if e.name not in self.SUBSTITUTE_WEEKEND:
                continue
            clash = e.day.weekday() >= 5 or (e.name == "어린이날" and count[e.day] > 1)
            if not clash:
                continue
            d = e.day + timedelta(days=1)
            while d.weekday() >= 5 or d in taken:
                d += timedelta(days=1)
            taken.add(d)
            out.append(CalendarEvent(d, f"대체공휴일({e.name})", "대체공휴일"))
        return out

    def covers_lunar(self, year: int) -> bool:
        return year in self.LUNAR


FINANCE_SCHEDULE = [(5, "종합소득세 신고·납부"), (6, "자동차세(1기)"), (7, "재산세(1기)"),
                    (9, "재산세(2기)"), (12, "자동차세(2기)")]


class KoreanCalendar:
    """
    매년 달력 데이터 자동 연동
    - 1순위: 공휴일 API(설·추석 등 음력 명절, 대체·임시공휴일 포함), 연도별 캐시
    - API 실패 시: 내장 예비 데이터(해당 연도 음력 명절이 없으면 경고)
    - 재정 일정(종합소득세·자동차세·재산세)과 사용자가 입력한 지출 이벤트를 함께 관리
    """

    def __init__(self, provider: Optional[HolidayProvider] = None):
        self.provider = provider
        self.fallback = BuiltinHolidayTable()
        self._cache: dict = {}
        self.sources: dict = {}
        self.user_events: list = []


    def __getstate__(self):
        """저장할 때 공휴일 API 제공자(인증 키 포함)는 빼고, 받아 둔 공휴일은 그대로 저장"""
        state = self.__dict__.copy()
        state["provider"] = None
        return state

    def holidays(self, year: int) -> list:
        if year not in self._cache:
            ev, src = None, ""
            if self.provider is not None:
                try:
                    ev, src = self.provider.fetch(year), self.provider.source
                except Exception as e:                              # 네트워크·인증 오류
                    src = f"API 실패({type(e).__name__}) → {self.fallback.source}"
            if ev is None:
                ev = self.fallback.fetch(year)
                src = src or self.fallback.source
                if not self.fallback.covers_lunar(year):
                    src += " — ⚠ 설·추석 날짜 없음, API 연동 필요"
            self._cache[year], self.sources[year] = ev, src
        return self._cache[year]

    def finance_events(self, year: int) -> list:
        out = []
        for m, name in FINANCE_SCHEDULE:
            last = (date(year + (m == 12), m % 12 + 1, 1) - timedelta(days=1))
            out.append(CalendarEvent(last, f"{name} 납부 기한", "재정 일정"))
        return out

    def add_user_event(self, day: date, name: str, amount: float, big: bool = False) -> CalendarEvent:
        ev = CalendarEvent(day, name, "사용자 지출", amount, big)
        self.user_events.append(ev)
        return ev

    def events_in_month(self, year: int, month: int) -> list:
        ev = [e for e in self.holidays(year) + self.finance_events(year) + self.user_events
              if e.day.year == year and e.day.month == month]
        return sorted(ev, key=lambda e: (e.day, e.kind))

    def month_key(self, year: int, month: int) -> str:
        """계절성 분석 키: 설·추석이 있는 달은 명절 이름, 그 외는 'M월' (명절이 1·2월, 9·10월로 옮겨 다녀도 추적)"""
        for e in self.holidays(year):
            if e.day.month == month and e.kind == "명절":
                return "설" if "설" in e.name else "추석"
        return f"{month}월"

    def user_amount(self, year: int, month: int) -> float:
        """계절성 적립 대상 사용자 지출 (목돈 지출은 Trigger C로 따로 관리하므로 제외)"""
        return sum(e.amount for e in self.user_events
                   if e.day.year == year and e.day.month == month and not e.big)

    def big_events(self) -> list:
        """목돈 지출 이벤트 → LiveLedger.register_event 로 넘겨 Trigger C(30일 이내) 감시"""
        return [(e.name, e.amount, e.day) for e in self.user_events if e.big]

    def text_month(self, year: int, month: int) -> list:
        """가계부 입력 창용 텍스트 달력 (공휴일·명절 = *, 재정 일정 = $, 사용자 지출 = ●)"""
        import calendar as _cal
        marks = {}
        for e in self.events_in_month(year, month):
            sym = {"명절": "*", "공휴일": "*", "대체공휴일": "*", "재정 일정": "$", "사용자 지출": "●"}[e.kind]
            marks[e.day.day] = marks.get(e.day.day, "") + sym
        lines = [f"{year}년 {month}월", " 일   월   화   수   목   금   토"]
        for week in _cal.Calendar(firstweekday=6).monthdayscalendar(year, month):
            lines.append(" ".join(f"{d:>2}{marks.get(d, ''):<2}" if d else "    " for d in week))
        for e in self.events_in_month(year, month):
            amt = f" {won(e.amount)}" if e.amount else ""
            lines.append(f"  {e.day:%m/%d} [{e.kind}] {e.name}{amt}{' (목돈)' if e.big else ''}")
        return lines

    def payload(self, years: list) -> dict:
        """가계부 입력 화면(캘린더)용 데이터"""
        return {
            "events": [dict(date=e.day.isoformat(), name=e.name, kind=e.kind, amount=e.amount, big=e.big)
                       for y in years for e in self.holidays(y) + self.finance_events(y)]
                      + [dict(date=e.day.isoformat(), name=e.name, kind=e.kind, amount=e.amount, big=e.big)
                         for e in self.user_events],
            "sources": {str(y): self.sources.get(y, "") for y in years},
        }


# ── 증시 달력: 한국(KRX)·미국(NYSE) 주말·공휴일·휴장일 → T+N 정산일·매도 후보·매수 집행일 ─────────
# 감시 기간(Trigger C 진입)은 달력 30일, 정산 관련 판단은 휴장일을 반영한 영업일
# 한국: 공휴일(특일 정보 API 또는 내장 예비 데이터) + KRX 휴장 규정(근로자의 날, 연말 휴장일)
# 미국: NYSE 휴장 규칙과 연방 공휴일(연준 결제 휴무) 규칙으로 해마다 계산
#       - 콜럼버스 데이·재향군인의 날: 증시는 열리지만 결제(정산)는 쉬는 날
# 규칙으로 알 수 없는 임시 휴장(예: 미국 국가 애도일)은 market_closures.json 에 추가하면 반영됩니다.
MARKET_KR, MARKET_US = "KR", "US"
MARKET_NAMES = {MARKET_KR: "한국", MARKET_US: "미국"}
C_WINDOW_DAYS = 30                   # Trigger C 감시 기간: 지출일까지 달력 30일 이내 (월급 주기 기준)
SPECIAL_CLOSURES = {                  # 규칙으로 계산할 수 없는 과거 임시 휴장
    MARKET_US: {"2025-01-09": "국가 애도일(카터 전 대통령) 휴장"},
}


def _nth_weekday(year: int, month: int, weekday: int, n: int) -> date:
    """n번째 요일 (n = -1 이면 마지막)"""
    if n > 0:
        d = date(year, month, 1)
        d += timedelta(days=(weekday - d.weekday()) % 7)
        return d + timedelta(weeks=n - 1)
    d = date(year + (month == 12), month % 12 + 1, 1) - timedelta(days=1)
    return d - timedelta(days=(d.weekday() - weekday) % 7)


def _easter(year: int) -> date:
    """부활절 (그레고리력, Anonymous Gregorian algorithm)"""
    a, b, c = year % 19, year // 100, year % 100
    d, e = b // 4, b % 4
    f = (b + 8) // 25
    g = (b - f + 1) // 3
    h = (19 * a + b - d - g + 15) % 30
    i, k = c // 4, c % 4
    l = (32 + 2 * e + 2 * i - h - k) % 7
    m = (a + 11 * h + 22 * l) // 451
    month = (h + l - 7 * m + 114) // 31
    return date(year, month, (h + l - 7 * m + 114) % 31 + 1)


def us_holidays(year: int) -> list:
    """
    미국 공휴일 → [(실제 날짜, 이름, 연방 공휴일 여부, NYSE 휴장 여부)]
    휴무일 이동: 연방 공휴일은 토→금·일→월, NYSE는 토요일이면 쉬지 않음(신정) 또는 금요일, 일요일이면 월요일
    """
    fixed = lambda m, d: date(year, m, d)
    rows = [(fixed(1, 1), "신정", True, True),
            (_nth_weekday(year, 1, 0, 3), "마틴 루서 킹 데이", True, True),
            (_nth_weekday(year, 2, 0, 3), "대통령의 날", True, True),
            (_easter(year) - timedelta(days=2), "성금요일", False, True),
            (_nth_weekday(year, 5, 0, -1), "메모리얼 데이", True, True),
            (fixed(7, 4), "독립기념일", True, True),
            (_nth_weekday(year, 9, 0, 1), "노동절(Labor Day)", True, True),
            (_nth_weekday(year, 10, 0, 2), "콜럼버스 데이", True, False),
            (fixed(11, 11), "재향군인의 날", True, False),
            (_nth_weekday(year, 11, 3, 4), "추수감사절", True, True),
            (fixed(12, 25), "크리스마스", True, True)]
    if year >= 2022:
        rows.append((fixed(6, 19), "준틴스", True, True))
    return sorted(rows)


def _observed(d: date, saturday_to_friday: bool = True) -> Optional[date]:
    if d.weekday() == 5:
        return d - timedelta(days=1) if saturday_to_friday else None
    if d.weekday() == 6:
        return d + timedelta(days=1)
    return d


class MarketCalendar:
    """
    한국·미국 증시 영업일 달력
      is_trading_day(market, d)     : 주말·공휴일·휴장일이 아닌 날
      add_settlement_days(...)      : T+N 정산일 (미국은 증시 휴장 + 연준 결제 휴무 제외)
      cash_available(...)           : 매도 대금을 원화로 쓸 수 있는 날 (미국 주식은 정산 후 다음 한국 영업일)
      business_days_until(...)      : 오늘 다음 날부터 지출일까지의 한국 영업일 수 (영업일 D-Day)
    """

    def __init__(self, kr_calendar: Optional["KoreanCalendar"] = None, extra_closures: Optional[dict] = None):
        self.kr = kr_calendar or KoreanCalendar()
        self.has_file = bool(extra_closures)
        merged = {m: dict(SPECIAL_CLOSURES.get(m, {}), **(extra_closures or {}).get(m, {}))
                  for m in (MARKET_KR, MARKET_US)}
        self.extra = {m: {date.fromisoformat(k): v for k, v in merged[m].items()} for m in merged}
        self._cache: dict = {}

    @classmethod
    def with_closure_file(cls, kr_calendar: Optional["KoreanCalendar"], path: str) -> "MarketCalendar":
        """market_closures.json: {"KR": {"YYYY-MM-DD": "이유"}, "US": {...}} — 규칙 밖 임시 휴장"""
        import json
        extra = {}
        if os.path.exists(path):
            with open(path, encoding="utf-8") as f:
                extra = json.load(f)
        return cls(kr_calendar, extra)

    # ── 연도별 휴장일 ──
    def closures(self, market: str, year: int) -> dict:
        """주말을 뺀 휴장일 {날짜: 이유}"""
        key = (market, year)
        if key not in self._cache:
            out = {}
            if market == MARKET_KR:
                for e in self.kr.holidays(year):
                    out.setdefault(e.day, e.name)
                out.setdefault(date(year, 5, 1), "근로자의 날 휴장")
                d = date(year, 12, 31)                      # 연말 휴장일: 12/31, 휴일이면 직전 영업일
                while d.weekday() >= 5 or d in out:
                    d -= timedelta(days=1)
                out[d] = "연말 휴장일"
            else:
                for d, name, _fed, nyse in us_holidays(year) + us_holidays(year + 1)[:1]:
                    if not nyse:
                        continue
                    obs = _observed(d, saturday_to_friday=name != "신정")
                    if obs is not None and obs.year == year:
                        out[obs] = name + ("" if obs == d else " (대체 휴장)")
            for d, why in self.extra.get(market, {}).items():
                if d.year == year:
                    out[d] = why
            out = {d: n for d, n in out.items() if d.weekday() < 5}
            self._cache[key] = out
        return self._cache[key]

    def us_settlement_holidays(self, year: int) -> dict:
        """미국 결제 휴무(연준): 연방 공휴일이 일요일이면 월요일, 토요일이면 쉬지 않음"""
        out = {}
        for d, name, fed, _ in us_holidays(year):
            if fed:
                obs = _observed(d, saturday_to_friday=False)
                if obs is not None and obs.weekday() < 5:
                    out[obs] = name
        return out

    def us_public_holidays(self, year: int) -> list:
        """화면 표시용 미국 공휴일 (연방 공휴일은 쉬는 날로 옮긴 날짜, 성금요일은 증시만 휴장)"""
        out = []
        for d, name, fed, _ in us_holidays(year):
            obs = _observed(d) if fed else d
            out.append((obs, name + (" (대체 휴일)" if obs != d else ""), fed))
        return out

    # ── 영업일 계산 ──
    def is_trading_day(self, market: str, d: date) -> bool:
        return d.weekday() < 5 and d not in self.closures(market, d.year)

    def is_settlement_day(self, market: str, d: date) -> bool:
        if not self.is_trading_day(market, d):
            return False
        return market != MARKET_US or d not in self.us_settlement_holidays(d.year)

    def next_trading_day(self, market: str, d: date, include: bool = True) -> date:
        d = d if include else d + timedelta(days=1)
        while not self.is_trading_day(market, d):
            d += timedelta(days=1)
        return d

    def add_trading_days(self, market: str, d: date, n: int) -> date:
        for _ in range(n):
            d = self.next_trading_day(market, d, include=False)
        return d

    def add_settlement_days(self, market: str, trade_day: date, n: int) -> date:
        d = trade_day
        for _ in range(n):
            d += timedelta(days=1)
            while not self.is_settlement_day(market, d):
                d += timedelta(days=1)
        return d

    def trade_date(self, market: Optional[str], day: date) -> date:
        """주문일 → 체결일 (휴장일에 낸 주문은 다음 영업일에 체결)"""
        return day if market is None else self.next_trading_day(market, day)

    def cash_available(self, market: Optional[str], settlement_days: int, day: date) -> date:
        """
        오늘(day) 매도 주문 → 매도 대금을 원화로 쓸 수 있는 날
          정산 0일(현금성·암호화폐): 당일
          한국 상장: 체결일 + 한국 영업일 N일
          미국 상장: 미국 체결일 + 미국 결제일 N일 → 다음 한국 영업일 (시차·환전)
        """
        if market is None or settlement_days <= 0:
            return day
        settle = self.add_settlement_days(market, self.trade_date(market, day), settlement_days)
        if market == MARKET_US:
            settle = self.next_trading_day(MARKET_KR, settle, include=False)
        return settle

    def business_days_until(self, today: date, due: date, market: str = MARKET_KR) -> int:
        """today 다음 날부터 due 까지의 영업일 수 (due 가 지났으면 음수)"""
        if due < today:
            return -1
        n, d = 0, today
        while d < due:
            d += timedelta(days=1)
            if self.is_trading_day(market, d):
                n += 1
        return n

    # ── 화면 표시용 ──
    def month_events(self, year: int, month: int) -> list:
        """가계부 달력용: 미국 공휴일, 한국·미국 증시 휴장일, 미국 결제 휴무일"""
        inm = lambda d: d.year == year and d.month == month
        out = []
        for d, name, fed in self.us_public_holidays(year):
            if inm(d):
                out.append({"date": d.isoformat(), "market": MARKET_US, "kind": "공휴일" if fed else "기념일",
                            "name": name})
        for m in (MARKET_KR, MARKET_US):
            for d, why in sorted(self.closures(m, year).items()):
                if inm(d):
                    out.append({"date": d.isoformat(), "market": m, "kind": "휴장", "name": why})
        us_closed = self.closures(MARKET_US, year)
        for d, name in sorted(self.us_settlement_holidays(year).items()):
            if inm(d) and d not in us_closed:
                out.append({"date": d.isoformat(), "market": MARKET_US, "kind": "결제 휴무",
                            "name": f"{name} — 증시는 열지만 결제(정산)는 쉼"})
        return sorted(out, key=lambda e: (e["date"], e["market"], e["kind"]))

    def source(self, year: int) -> str:
        kr = self.kr.sources.get(year) or (self.kr.holidays(year) and self.kr.sources.get(year, ""))
        extra = " + market_closures.json" if self.has_file else ""
        return (f"한국 휴장일: 공휴일({kr}) + KRX 규정(근로자의 날·연말 휴장일) · "
                f"미국 휴장일: NYSE 휴장 규칙·연방 공휴일 규칙으로 계산{extra}")


_MARKET_CALENDAR: Optional[MarketCalendar] = None


def market_calendar() -> MarketCalendar:
    global _MARKET_CALENDAR
    if _MARKET_CALENDAR is None:
        _MARKET_CALENDAR = MarketCalendar()
    return _MARKET_CALENDAR


def set_market_calendar(cal: MarketCalendar) -> None:
    """웹 서비스가 공휴일 API를 쓰는 KoreanCalendar 로 만든 달력을 엔진 전체에 연결"""
    global _MARKET_CALENDAR
    _MARKET_CALENDAR = cal


def asset_market(overseas: bool, settlement_days: int) -> Optional[str]:
    """정산일 계산에 쓸 시장: 정산 0일(현금성·암호화폐)은 휴장과 무관"""
    if settlement_days <= 0:
        return None
    return MARKET_US if overseas else MARKET_KR


class SettleDeadline(int):
    """
    목돈 지출 마감: 정수값은 남은 영업일 수(기존 비교 호환), due·trade_day 가 있으면 날짜로 정산 가능 여부 판단
    """
    def __new__(cls, days: int, due: Optional[date] = None, trade_day: Optional[date] = None):
        obj = int.__new__(cls, days)
        obj.due, obj.trade_day = due, trade_day
        return obj

    def __getnewargs__(self):
        return (int(self), self.due, self.trade_day)


def cash_date(h, trade_day: date) -> date:
    """보유 자산 h 를 trade_day 에 매도 주문했을 때 원화로 쓸 수 있는 날"""
    return market_calendar().cash_available(asset_market(h.overseas, h.settlement_days), h.settlement_days, trade_day)


def settles_in_time(h, deadline) -> bool:
    """목돈 지출일 전에 매도 대금이 들어오는지 (날짜 정보가 있으면 휴장일까지 반영)"""
    if deadline is None:
        return True
    due = getattr(deadline, "due", None)
    if due is not None:
        return cash_date(h, deadline.trade_day or clock_today()) <= due
    return h.settlement_days <= deadline


def upcoming_big_expenses(events, today: date) -> tuple:
    """
    목돈 지출 일정 [(이름, 금액, 지출일)] → Trigger C 감시 대상 (지출일까지 달력 30일 이내)
    반환: (합계, D-Day(달력), 남은 영업일 수, 가장 가까운 지출일, 대상 목록)
    """
    cal = market_calendar()
    near = []
    for name, amount, due in events:
        days = (due - today).days
        if 0 <= days <= C_WINDOW_DAYS:
            near.append((name, amount, due, days, cal.business_days_until(today, due)))
    if not near:
        return 0.0, None, None, None, []
    first = min(near, key=lambda x: x[2])
    return sum(x[1] for x in near), first[3], first[4], first[2], near


def schedule_orders(orders: list, portfolio: Optional["Portfolio"], today,
                    instruments: Optional[dict] = None) -> None:
    """
    주문마다 실제 집행일(exec_date)·매도 대금 입금일(cash_date) 계산 — 주말·휴장일 반영
      T+0 주문: 해당 시장의 다음 영업일
      T+N 매수(매도 대금으로 사는 주문): 같은 제안 안 매도들의 대금이 들어오는 날 이후 첫 영업일
    today 에 시각(datetime)을 주면 한국 장 마감(15:00) 뒤의 한국 주문은 다음 날로 넘김
    (승인 시점 재계산에 사용 — 미국 주문은 그날 밤 미국 장에서 체결되므로 그대로)
    """
    cal = market_calendar()
    if isinstance(today, datetime):
        after_close = today.time() > TRADING_WINDOW[1]
        today = today.date()
    else:
        after_close = False
    kr_day = today + timedelta(days=1) if after_close else today

    def base(market: Optional[str]) -> date:
        return kr_day if market == MARKET_KR else today
    overseas = {}
    for src in (instruments or {}).values():
        overseas[src.ticker] = src.overseas
    if portfolio is not None:
        for h in portfolio.holdings:
            overseas[h.ticker] = h.overseas

    def mkt(o) -> Optional[str]:
        if o.asset_class == CASH:
            return None
        return MARKET_US if overseas.get(o.ticker) else MARKET_KR

    funds = today
    for o in orders:
        if o.side == "매도" and o.day == 0 and portfolio is not None:
            h = portfolio.find(o.ticker)
            if h is not None:
                o.cash_date = cash_date(h, base(h.market))
                funds = max(funds, o.cash_date)
    for o in orders:
        m = mkt(o)
        if o.day == 0:
            o.exec_date = cal.trade_date(m, base(m))
        else:
            start = funds if funds > today else \
                cal.add_trading_days(MARKET_KR, cal.next_trading_day(MARKET_KR, kr_day), o.day)
            o.exec_date = cal.trade_date(m, start)


def late_sells(orders: list) -> list:
    """
    목돈 지출에 맞춰 판 매도 중, 지금 기준 대금 입금일(cash_date)이 지출일보다 늦어진 주문
    (schedule_orders 로 날짜를 다시 계산한 뒤 호출)
    """
    out = []
    for o in orders:
        due = getattr(o.deadline_days, "due", None)
        if o.side == "매도" and due is not None and o.cash_date is not None and o.cash_date > due:
            out.append(o)
    return out


def _md(d: date) -> str:
    return f"{d:%m/%d}({'월화수목금토일'[d.weekday()]})"


def export_calendar_html(html_path: str, cal: "KoreanCalendar", planner: Optional["SeasonalPlanner"],
                         years: list, today: date) -> None:
    """가계부 입력 캘린더 화면(ledger_calendar.html)에 달력·계절성 데이터를 넣어 갱신"""
    import json
    data = cal.payload(years)
    seasonal = {}
    if planner is not None:
        for y in years:
            for m in range(1, 13):
                extra, why = planner.expected_extra(y, m)
                pat = planner.spikes().get(planner._key(y, m), 0.0)
                if pat > 0:        # 화면에서 사용자 입력과 비교하므로 패턴 추정치만 넘김
                    seasonal[f"{y}-{m:02d}"] = {"extra": round(pat), "why": why if "패턴" in why
                                                else f"{planner._key(y, m)} 지출 패턴"}
    data.update(seasonal=seasonal, today=today.isoformat(), max_hold=SEASONAL_MAX_HOLD)
    with open(html_path, encoding="utf-8") as f:
        html = f.read()
    start = html.index('<script id="calendar-data" type="application/json">') + \
        len('<script id="calendar-data" type="application/json">')
    end = html.index("</script>", start)
    html = html[:start] + json.dumps(data, ensure_ascii=False) + html[end:]
    with open(html_path, "w", encoding="utf-8") as f:
        f.write(html)


def import_calendar_json(text: str, cal: "KoreanCalendar") -> dict:
    """캘린더 화면에서 내보낸 JSON → 사용자 지출 이벤트 등록 + 월별 LedgerSnapshot 반환"""
    import json
    data = json.loads(text)
    cal.user_events = []
    for e in data.get("user_events", []):
        cal.add_user_event(date.fromisoformat(e["date"]), e["name"], float(e.get("amount", 0)), bool(e.get("big")))
    snaps = {}
    for period, L in data.get("ledgers", {}).items():
        snaps[period] = LedgerSnapshot(L["monthly_income"], L["essential_expense"], L.get("emergency_balance"),
                                       L.get("emergency_deposit", 0.0), L.get("emergency_withdrawal", 0.0),
                                       period=period, total_expense=L.get("total_expense", 0.0))
    return snaps


# ── 계절성·비정기 지출 대비 ──────────────────────────────────────
SEASON_LABELS = {1: "설 명절(연도별 1~2월)", 2: "설 명절", 5: "가정의 달(어버이날·어린이날)·종합소득세 신고",
                 7: "재산세(1기)·휴가", 8: "휴가", 9: "추석 명절(연도별 9~10월)·재산세(2기)", 10: "추석 명절",
                 12: "연말 경조사·자동차세"}
SEASONAL_SPIKE_RATIO = 0.15        # 평소(중앙값)보다 15% 이상 지출이 많은 달을 비정기 지출 달로 판단
SEASONAL_MIN_EXTRA = 300_000       # 또는 초과 지출이 30만 원 이상
SEASONAL_MAX_HOLD = 0.7            # 직전 달 순잉여금 중 최대 70%까지 현금으로 적립 (나머지는 스마트 바이)


class SeasonalPlanner:
    """
    1년치 가계부 지출 패턴 스캔 → 비정기 지출이 몰리는 달을 찾아 그 직전 달에 현금 선적립
    - 달력 연동: 설·추석이 있는 달은 명절 이름으로 묶어 분석하므로, 명절이 해마다
      1·2월 또는 9·10월로 옮겨 다녀도 올해의 명절 달을 정확히 찾음
    - 사용자가 달력에 입력한 지출 이벤트 금액도 반영 (패턴 추정치와 입력액 중 큰 값)
      평소 지출 = 최근 12개월 월 지출의 중앙값
      예상 초과 지출(키) = (해당 키 달의 지출 − 평소 지출)의 평균   (15% 또는 30만 원 이상일 때만)
      적립액 = min(max(다음 달 패턴 초과 지출, 다음 달 사용자 입력 지출), 순잉여금 × 70%)
      스마트 바이 투입액 = 순잉여금 − 적립액
    """

    def __init__(self, history: Optional[list] = None, calendar: Optional[KoreanCalendar] = None):
        self.history = list(history or [])          # [(YYYY-MM, 월 지출 합계)]
        self.calendar = calendar

    def add(self, period: str, expense: float) -> None:
        self.history = [(p, e) for p, e in self.history if p != period] + [(period, expense)]

    def _key(self, year: int, month: int) -> str:
        return self.calendar.month_key(year, month) if self.calendar else f"{month}월"

    def baseline(self) -> Optional[float]:
        recent = sorted(self.history, key=lambda x: x[0])[-12:]
        if len(recent) < 12:
            return None
        vals = sorted(e for _, e in recent)
        return (vals[5] + vals[6]) / 2

    def spikes(self) -> dict:
        """분석 키(설·추석 또는 'M월') → 예상 초과 지출"""
        base = self.baseline()
        if base is None:
            return {}
        by_key = {}
        for p, e in self.history:
            by_key.setdefault(self._key(int(p[:4]), int(p[5:7])), []).append(e - base)
        out = {}
        for k, extras in by_key.items():
            avg = sum(extras) / len(extras)
            if avg >= max(base * SEASONAL_SPIKE_RATIO, SEASONAL_MIN_EXTRA):
                out[k] = avg
        return out

    def expected_extra(self, year: int, month: int) -> tuple:
        """(예상 초과 지출, 근거)"""
        key = self._key(year, month)
        pattern = self.spikes().get(key, 0.0)
        user = self.calendar.user_amount(year, month) if self.calendar else 0.0
        if user > pattern:
            return user, f"달력 입력 지출 {won(user)}"
        if pattern > 0:
            label = key if key in ("설", "추석") else SEASON_LABELS.get(month, "비정기 지출")
            return pattern, f"{label} 지출 패턴"
        return 0.0, ""

    def is_spike_month(self, period: str) -> bool:
        y, m = int(period[:4]), int(period[5:7])
        return self.expected_extra(y, m)[0] > 0

    def plan(self, period: str, free_cash: float) -> tuple:
        """period(방금 마감한 달)의 순잉여금 배분: (스마트 바이 투입액, 현금 적립액, 안내)"""
        if not period or free_cash <= 0:
            return free_cash, 0.0, ""
        y, m = int(period[:4]), int(period[5:7])
        ny, nm = (y + 1, 1) if m == 12 else (y, m + 1)
        extra, why = self.expected_extra(ny, nm)
        if extra <= 0:
            return free_cash, 0.0, ""
        reserve = min(extra, free_cash * SEASONAL_MAX_HOLD)
        note = (f"다음 달({ny}-{nm:02d}, {why}) 예상 초과 지출 {won(extra)} → 순잉여금 {won(free_cash)} 중 "
                f"{won(reserve)} 현금 적립, 스마트 바이 투입 {won(free_cash - reserve)} "
                f"({(free_cash - reserve) / free_cash * 100:.0f}%)")
        return free_cash - reserve, reserve, note

    def calendar_plan(self, start: date, months: int = 12) -> list:
        base = self.baseline()
        if base is None:
            return ["지출 이력 12개월 미만 → 계절성 분석 대기"]
        lines = [f"평소 월 지출(중앙값) {won(base)}"]
        y, m = start.year, start.month
        for _ in range(months):
            extra, why = self.expected_extra(y, m)
            if extra > 0:
                py, pm = (y - 1, 12) if m == 1 else (y, m - 1)
                lines.append(f"{y}-{m:02d} {why}: 예상 초과 {won(extra)} → {py}-{pm:02d} 순잉여금에서 선적립")
            if self.calendar:
                for e in self.calendar.user_events:
                    if e.big and e.day.year == y and e.day.month == m:
                        lines.append(f"{y}-{m:02d} 목돈 지출 '{e.name}' {won(e.amount)} → 계절성 적립 대신 "
                                     f"Trigger C(30일 전부터) 감시")
            y, m = (y + 1, 1) if m == 12 else (y, m + 1)
        return lines


# ── 비정기 수입 사용 순서 ─────────────────────────────────────────
IRREGULAR_TAX_RATIO = 0.15          # 사업·용역 소득 중 종합소득세 대비로 남길 비율 (10~15% 권장)
IRREGULAR_LUMP_RATIO = 0.10         # 투자 자산의 10% 이상이면 한 번에 넣지 않고 분할 매수
IRREGULAR_DCA_ROUNDS = 3            # 분할 매수 횟수 (이번 달 포함)
IRREGULAR_UPCOMING_DAYS = 90        # 이 기간 안의 목돈 지출 일정은 비정기 수입으로 미리 채움
TAXABLE_IRREGULAR_KEYWORDS = ("사업", "용역", "프리랜서", "외주", "강의", "원고", "정산", "자문")


@dataclass
class IrregularPlan:
    amount: float
    to_emergency: float = 0.0
    to_upcoming: float = 0.0
    to_seasonal: float = 0.0
    to_tax: float = 0.0
    invest_now: float = 0.0
    invest_later: list = field(default_factory=list)

    def lines(self) -> list:
        if self.amount <= 0:
            return []
        out = [f"비정기 수입 {won(self.amount)} 사용 순서 (등급·Buffer·트리거 판단에는 넣지 않음)"]
        for label, v in (("① 비상금 부족분", self.to_emergency), ("② 예정된 목돈 지출", self.to_upcoming),
                         ("② 다음 달 비정기 지출 대비", self.to_seasonal), ("③ 세금 몫 (종합소득세 대비)", self.to_tax)):
            if v > 0.5:
                out.append(f"  {label}: {won(v)}")
        if self.invest_later:
            out.append(f"  ④ 스마트 바이: 이번 달 {won(self.invest_now)} + 다음 {len(self.invest_later)}개월 "
                       f"{won(self.invest_later[0])}씩 분할 (투자 자산의 {int(IRREGULAR_LUMP_RATIO * 100)}% 이상 목돈)")
        elif self.invest_now > 0.5:
            out.append(f"  ④ 스마트 바이: {won(self.invest_now)}")
        return out


def plan_irregular_income(amount: float, taxable: float = 0.0, *, emergency_shortage: float = 0.0,
                          upcoming_shortfall: float = 0.0, seasonal_shortfall: float = 0.0,
                          portfolio_total: float = 0.0, tax_ratio: float = IRREGULAR_TAX_RATIO,
                          lump_ratio: float = IRREGULAR_LUMP_RATIO,
                          rounds: int = IRREGULAR_DCA_ROUNDS) -> IrregularPlan:
    """
    비정기 수입 사용 순서 — 안전에 필요한 몫을 먼저 채우고 남는 돈을 투자
      ① 비상금 부족분  ② 예정된 지출(목돈 일정·다음 달 비정기 지출 대비금 부족분)
      ③ 세금 몫: 사업·용역 소득 × 15%  ④ 나머지 → 스마트 바이
         (투자 자산의 10% 이상이면 3회 분할: 이번 달 1/3, 다음 두 달 1/3씩)
    """
    plan = IrregularPlan(max(0.0, amount))
    left = plan.amount
    for attr, need in (("to_emergency", emergency_shortage), ("to_upcoming", upcoming_shortfall),
                       ("to_seasonal", seasonal_shortfall), ("to_tax", max(0.0, taxable) * tax_ratio)):
        take = min(left, max(0.0, need))
        setattr(plan, attr, take)
        left -= take
    if left > 0.5 and portfolio_total > 0 and left >= portfolio_total * lump_ratio and rounds > 1:
        plan.invest_now = left / rounds
        plan.invest_later = [left / rounds] * (rounds - 1)
    else:
        plan.invest_now = left
    return plan


def smart_buy_amounts(free_cash: float, gaps: dict, portfolio: Optional["Portfolio"] = None,
                      targets: Optional[dict] = None) -> dict:
    """
    BuyAmount_i = Free_Cash × |Gap_i| ÷ Σ_{j∈미달} |Gap_j|     (Gap_i < 0 인 자산만, 나머지는 0)
      - Gap_i = Current_Ratio_i − Target_Ratio_i (%p)
      - 많이 모자란 자산일수록 더 많이 배분, 매도 없이 비중을 목표로 수렴
    과매수 방지(portfolio·targets 제공 시):
      - 각 자산은 '새 돈을 넣은 뒤 목표 비중이 되는 금액'까지만 매수
        상한_i = Target_i × (현재 총자산 + Free_Cash) − 현재 평가액_i
      - 상한에 걸려 남은 돈은 목표 비중대로 전 자산에 나눠 배분 (포트폴리오가 목표 비율로 함께 커짐)
    """
    under = {c: -g for c, g in gaps.items() if g < 0}
    total_gap = sum(under.values())
    if free_cash <= 0:
        return {}
    if total_gap <= 0:
        base = {}
    else:
        base = {c: free_cash * g / total_gap for c, g in under.items()}
    if portfolio is None or targets is None:
        return base
    new_total = portfolio.total() + free_cash
    cv = portfolio.class_values()
    caps = {c: max(0.0, targets.get(c, 0) / 100 * new_total - cv[c]) for c in ASSET_CLASSES}
    out = {c: min(a, caps[c]) for c, a in base.items()}
    left = free_cash - sum(out.values())
    if left > 0.5:
        room = {c: caps[c] - out.get(c, 0.0) for c in ASSET_CLASSES if caps[c] - out.get(c, 0.0) > 0}
        room_sum = sum(room.values())
        for c, r in room.items():                      # 목표까지 남은 여력에 비례 배분
            out[c] = out.get(c, 0.0) + left * r / room_sum if room_sum else 0.0
    return {c: a for c, a in out.items() if a > 0.5}


def smart_buy_table(free_cash: float, gaps: dict, portfolio: Optional["Portfolio"] = None,
                    targets: Optional[dict] = None) -> list:
    amounts = smart_buy_amounts(free_cash, gaps, portfolio, targets)
    under_sum = sum(-g for g in gaps.values() if g < 0)
    lines = [f"스마트 바이: Free_Cash {won(free_cash)} × |Gap_i| ÷ Σ|Gap_미달| ({under_sum:.2f}%p)"]
    for c, a in amounts.items():
        if gaps.get(c, 0) < 0 and under_sum > 0:
            raw = free_cash * abs(gaps[c]) / under_sum
            capped = " (목표 도달 상한 적용)" if a < raw - 0.5 else ""
            lines.append(f"  {c}: {won(free_cash)} × {abs(gaps[c]):.2f} ÷ {under_sum:.2f} = {won(raw)}"
                         f" → {won(a)}{capped}")
        else:
            lines.append(f"  {c}: 상한 초과분 재배분 {won(a)} (목표 비중대로)")
    return lines


def smart_buy(free_cash: float, portfolio: Portfolio, targets: dict, instruments: dict):
    """비중 미달 자산(Gap<0)에 BuyAmount_i 만큼 매수 주문 생성 (최소 주문 단위 가드·자투리 CMA 흡수)"""
    gaps = portfolio.gaps(targets)
    amounts = smart_buy_amounts(free_cash, gaps, portfolio, targets)
    return allocate_buys(free_cash, amounts, instruments, 0, "스마트 바이")


REBALANCE_PERIOD_MONTHS = 6    # 정기 리밸런싱 주기
PERIODIC_MIN_GAP = REBALANCE_BAND   # 정기 점검 때도 ±5%p 이상일 때만 매매 (거래비용 고려)


def add_months(d: date, months: int) -> date:
    y, m = divmod(d.month - 1 + months, 12)
    y += d.year
    m += 1
    last = [31, 29 if y % 4 == 0 and (y % 100 != 0 or y % 400 == 0) else 28,
            31, 30, 31, 30, 31, 31, 30, 31, 30, 31][m - 1]
    return date(y, m, min(d.day, last))


def mechanical_rebalance(portfolio: Portfolio, targets: dict, instruments: dict, periodic_due: bool) -> tuple:
    """
    기계적 리밸런싱 (목표 비중은 등급에 따라 고정)
    ① 밴드 이탈: 어떤 자산이든 |Gap_i| ≥ 5%p
         Gap_i ≥ +5%p 자산을 목표까지 일부 매도해 현금 확보(T일) → Gap_i ≤ −5%p 자산 매수(T+2)
    ② 정기 주기(6개월) 도래: 전 자산 비중을 전면 점검하되, 거래비용을 고려해
       매매는 역시 ±5%p 이상 이탈한 자산에만 허용 (그 미만 오차는 스마트 바이로 흡수)
    반환: (주문, 안내, 사유: "밴드 이탈" / "정기 리밸런싱" / "")
    """
    gaps = portfolio.gaps(targets)
    breach = any(abs(g) >= REBALANCE_BAND for g in gaps.values())
    if breach:
        orders, notes = band_rebalance(portfolio, targets, instruments, band=REBALANCE_BAND)
        return orders, notes, "밴드 이탈"
    if periodic_due:
        worst = max(gaps.items(), key=lambda kv: abs(kv[1]))
        return [], [f"정기 리밸런싱 점검(6개월): 최대 오차 {worst[0]} {worst[1]:+.1f}%p < ±{REBALANCE_BAND:.0f}%p "
                    f"→ 거래비용을 고려해 매매 없음 (오차는 스마트 바이로 흡수)"], "정기 리밸런싱"
    return [], [f"밴드 이탈 없음 (모든 자산 ±{REBALANCE_BAND:.0f}%p 이내)"], ""


def band_rebalance(portfolio: Portfolio, targets: dict, instruments: dict, days_since_last: int = 0,
                   band: float = REBALANCE_BAND, label: str = "밴드 리밸런싱"):
    """Gap_i ≥ +band 자산을 목표까지 일부 매도 → Gap_i ≤ −band 자산 매수 (정산 T+2 후)"""
    gaps = portfolio.gaps(targets)
    total = portfolio.total()
    over = {c: g for c, g in gaps.items() if g >= band}
    under = {c: -g for c, g in gaps.items() if g <= -band}
    if not over and not under:
        return [], [f"{label}: 이탈 없음"]
    notes = []
    if not over:   # 미달만 있으면 가장 초과된 자산에서 재원 조달
        over = {c: g for c, g in gaps.items() if g > 0}
    if not under:
        under = {c: -g for c, g in gaps.items() if g < 0}

    sells = []
    need_total = sum(under.values()) * total / 100
    over_total = sum(over.values())
    for c, g in over.items():
        amount = min(total * g / 100, need_total * g / over_total)
        cands = [h for h in portfolio.holdings if h.asset_class == c and not h.locked
                 and (c == CASH or h.daily_trading_value >= MIN_DAILY_TRADING_VALUE)]
        # 절세 계좌 우선 → 비용 비율 낮은 순
        # 절세 계좌 우선 → CostPenal_i(세금·수수료 부담) 낮은 순
        cands.sort(key=lambda h: tax_aware_sell_key(h, min(amount, h.value)))
        for h in cands:
            if amount <= 0:
                break
            o = _sell_order(h, min(amount, h.value), 0, f"{label} 매도 (Gap {gaps[c]:+.1f}%p → 목표)",
                            round_up=False, purpose=PURPOSE_FUNDING)
            if o:
                sells.append(o)
                amount -= o.amount
    settle = max((portfolio.find(o.ticker).settlement_days for o in sells if o.asset_class != CASH), default=0)
    buys, n = allocate_buys(sum(o.amount for o in sells), under, instruments, settle, f"{label} 매수")
    # 매도 대금은 그 계좌 안에서 재투자 (절세 계좌에 신규 납입하는 것이 아니므로 납입 한도와 무관)
    by_acct = {}
    for o in sells:
        h = portfolio.find(o.ticker)
        a = h.account if h else "일반"
        by_acct[a] = by_acct.get(a, 0.0) + o.amount
    src = max(by_acct, key=by_acct.get) if by_acct else "일반"
    for b in buys:
        if b.asset_class != CASH:
            b.account = src if not (b.account == "일반" and src != "일반") else "일반"
    return sells + buys, notes + n


# ── 실행 가드 & 1-Click 승인 ───────────────────────────────────────
def is_trading_window(now: datetime, market: str = "KR") -> bool:
    """발주 가능 시간: 한국 영업일(주말·공휴일·휴장일 제외) 10:00~15:00"""
    return market_calendar().is_trading_day(market, now.date()) and \
        TRADING_WINDOW[0] <= now.time() <= TRADING_WINDOW[1]


@dataclass
class OrderProposal:
    orders: list
    title: str = "매매 제안"
    extra: list = field(default_factory=list)   # 세금·손실·권고 등 추가 안내

    def estimated_cost(self, portfolio: Portfolio, realized_overseas_ytd: float = 0.0) -> float:
        """예상 세금·수수료 — 해외주식은 여러 매도의 손익을 합산해 비과세 한도 반영"""
        cost, ytd = 0.0, realized_overseas_ytd
        for o in self.orders:
            if o.asset_class == CASH:
                continue
            h = portfolio.find(o.ticker)
            if o.side == "매도" and h:
                cost += h.estimate_tax(o.amount, ytd) + h.estimate_fee(o.amount)
                if h.overseas and not h.tax_advantaged:
                    ytd += o.amount * (1 - h.avg_price / h.price)
            else:
                cost += o.amount * 0.00015
        return cost

    def render(self, portfolio: Portfolio) -> str:
        lines = [f"  📩 {self.title}"] + [f"    {o}" for o in self.orders]
        if self.extra:
            lines += [f"    {x}" for x in self.extra]
        else:
            lines.append(f"    예상 세금·수수료 ≈ {won(self.estimated_cost(portfolio))}")
        return "\n".join(lines)


class BrokerAPI:
    """증권사 Open API 연동 인터페이스 (실제 구현은 증권사별로 작성)"""
    def place_order(self, order: Order) -> str:
        raise NotImplementedError

    def get_quote(self, ticker: str) -> Optional[float]:
        """현재가 (조회 불가 시 None)"""
        return None

    def get_deposit(self) -> float:
        """주문 가능 예수금 (정산 완료된 현금)"""
        return math.inf


class MockBroker(BrokerAPI):
    def __init__(self, quotes: Optional[dict] = None, deposit: float = math.inf):
        self.quotes = dict(quotes or {})
        self.deposit = deposit

    def get_quote(self, ticker: str) -> Optional[float]:
        return self.quotes.get(ticker)

    def get_deposit(self) -> float:
        return self.deposit

    def place_order(self, order: Order) -> str:
        q = order.quantity
        qty = f"{q:,.0f}" if float(q).is_integer() else f"{q:,.4f}"
        return f"접수 완료: {order.side} {order.name} {qty}"


PRICE_DEVIATION_LIMIT = 3.0      # 제안 시점 대비 현재가 변동 한도(%) — 초과 시 보류·재승인


def pre_trade_check(orders: list, broker: BrokerAPI, portfolio: Optional[Portfolio] = None) -> tuple:
    """
    발주 직전 점검 (장중 실제 발주 순간에 실행)
    ① 현재가 조회: 제안 가격 대비 ±3% 넘게 움직였으면 보류 → 재승인 요청
    ② 수량 재계산: 제안 금액을 유지하도록 현재가로 수량 조정
         - 유동성 확보 매도(Trigger A·C): 필요 금액을 채우도록 올림
         - 그 외 매도·매수: 내림 (보유 수량 한도)
    ③ 예수금 확인: 매수 총액(수수료 포함)이 주문 가능 예수금을 넘으면 비례 축소,
         1주 미만이 된 주문은 매수 유예 (남은 금액은 예수금으로 대기)
    ④ 매도 수량은 보유 수량을 넘지 않도록 제한 (portfolio 제공 시)
    ⑤ 유동성 확보 매도가 보유 수량 한도에 걸려 필요 금액을 못 채우면,
       부족분을 다른 보유 종목에서 추가 매도 — 원래 승인에 없던 종목이므로 즉시 발주하지 않고
       '대체 매도 승인 요청' 푸시 알림으로 한 번 더 승인받음
    반환: (발주할 주문, 보류 주문, 안내, 별도 승인이 필요한 대체 매도)
    현금성(CMA) 이체는 가격·수량 점검 대상이 아님
    """
    go, held, notes = [], [], []
    shortfalls = []                    # [(원 종목명, 부족 금액)] 유동성 매도 부족분
    for o in orders:
        if o.asset_class == CASH:
            go.append(o)
            continue
        q = broker.get_quote(o.ticker)
        if q is None or q <= 0:
            go.append(o)
            continue
        dev = (q / o.price - 1) * 100
        if abs(dev) > PRICE_DEVIATION_LIMIT:
            held.append(o)
            notes.append(f"가격 급변 {dev:+.1f}% (한도 ±{PRICE_DEVIATION_LIMIT:.0f}%): {o.side} {o.name} → 보류, 재승인 필요")
            continue
        amt = o.quantity * o.price
        n = copy.copy(o)
        n.price = q
        frac = float(o.quantity) != int(o.quantity) or o.asset_class == CRYPTO
        if frac:
            n.quantity = amt / q
        elif o.side == "매도" and o.purpose == PURPOSE_LIQUIDITY:
            n.quantity = math.ceil(amt / q)
        else:
            n.quantity = math.floor(amt / q)
        if o.side == "매도" and portfolio is not None:
            h = portfolio.find(o.ticker)
            if h is not None and n.quantity > h.quantity:
                n.quantity = h.quantity
                notes.append(f"{o.name}: 보유 수량 {h.quantity:,.4g} 한도로 매도 수량 제한")
        if o.side == "매도" and o.purpose == PURPOSE_LIQUIDITY:
            gap = amt - n.quantity * q
            if gap > 0.5:
                shortfalls.append((o.name, gap))
        if n.quantity != o.quantity:
            notes.append(f"현재가 {won(q)} ({dev:+.1f}%) 반영: {o.side} {o.name} {o.quantity:,.4g} → {n.quantity:,.4g}")
        if n.quantity > 0:
            go.append(n)
        else:
            notes.append(f"{o.name}: 현재가 기준 1주 미만 → 주문 제외")

    subs = []
    if shortfalls:
        subs, sub_notes = substitute_liquidity_sells(shortfalls, go, broker, portfolio)
        notes += sub_notes

    buys = [o for o in go if o.side == "매수" and o.asset_class != CASH]
    need = sum(o.amount * (1 + 0.00015) for o in buys)
    deposit = broker.get_deposit()
    if buys and need > deposit:
        ratio = max(0.0, deposit / need)
        notes.append(f"예수금 {won(deposit)} < 매수 필요액 {won(need)} → 매수 수량 {ratio * 100:.0f}%로 축소")
        adjusted = []
        for o in go:
            if o in buys:
                n = copy.copy(o)
                n.quantity = (o.quantity * ratio) if o.asset_class == CRYPTO else math.floor(o.quantity * ratio)
                if n.quantity <= 0:
                    notes.append(f"{o.name}: 예수금 부족으로 1주 미만 → 매수 유예 (예수금 대기)")
                    continue
                adjusted.append(n)
            else:
                adjusted.append(o)
        go = adjusted
    return go, held, notes, subs


def substitute_liquidity_sells(shortfalls: list, planned: list, broker: BrokerAPI,
                               portfolio: Optional[Portfolio]) -> tuple:
    """
    유동성 확보 매도(비상금 복구·목돈 마련)의 부족분을 다른 종목에서 추가 매도
    대체 종목 선택 순서 (Trigger A 매도 순서와 같은 원칙):
      ① 손실 −10% 이하 종목은 최후 순위
      ② 정산이 빠른 종목 우선 (필요 시점까지 현금화)
      ③ 변동성이 낮은 종목 우선
      ④ 세금·수수료 비율이 낮은 종목 우선
      ⑤ 수익률이 높은 종목 우선
    제외: 현금성 자산, 매도 금지 자산, 이번 주문에서 이미 매도하는 수량, 같은 주문에서 매수하는 종목,
          목돈 지출 D-Day보다 정산일(T+N)이 늦은 종목
    가격은 발주 직전 현재가(조회 불가 시 보유 평가 가격) 기준, 필요 금액을 채우도록 올림
    반환: (추가 매도 주문, 안내)
    """
    total_gap = sum(g for _, g in shortfalls)
    names = ", ".join(n for n, _ in shortfalls)
    if portfolio is None:
        return [], [f"유동성 매도 부족분 {won(total_gap)} ({names}): 보유 종목 정보가 없어 대체 매도 불가"]
    already = {}
    buying = {o.ticker for o in planned if o.side == "매수"}      # 같은 날 사는 종목은 팔지 않음
    for o in planned:
        if o.side == "매도":
            already[o.ticker] = already.get(o.ticker, 0.0) + o.quantity

    def avail(h: Holding) -> float:
        return max(0.0, h.quantity - already.get(h.ticker, 0.0))

    def key(h: Holding):
        cost = (h.estimate_tax(h.value) + h.estimate_fee(h.value)) / h.value if h.value else 0.0
        return (h.profit_pct <= -10, h.settlement_days, not h.tax_advantaged,
                cost_penalty(h, min(total_gap, h.value)), h.volatility, -h.profit_pct)

    deadline = min((o.deadline_days for o in planned if o.deadline_days is not None), default=None)
    cands = sorted([h for h in portfolio.holdings
                    if h.asset_class != CASH and not h.locked and avail(h) > 0
                    and h.ticker not in buying
                    and settles_in_time(h, deadline)], key=key)
    subs, notes = [], [f"유동성 매도 부족분 {won(total_gap)} ({names}) → 다른 종목에서 추가 매도"]
    need = total_gap
    for h in cands:
        if need <= 0.5:
            break
        q = broker.get_quote(h.ticker) or h.price
        cap = avail(h)
        qty = min(cap, need / q) if h.fractional else min(cap, math.ceil(need / q))
        if qty <= 0:
            continue
        o = Order("매도", h.ticker, h.name, h.asset_class, qty, q, 0,
                  f"부족분 대체 매도 (원 주문: {names})", PURPOSE_LIQUIDITY, deadline_days=deadline)
        subs.append(o)
        need -= o.amount
        notes.append(f"대체 매도: {h.name} {qty:,.4g} ≈ {won(o.amount)} (수익률 {h.profit_pct:+.1f}%, T+{h.settlement_days})")
    if need > 0.5:
        notes.append(f"⚠ 대체 가능한 보유 종목 부족: {won(need)} 미충족 → 사용자 확인 필요")
    return subs, notes


def split_orders_for_ledger_freeze(orders: list, frozen: bool) -> tuple:
    """
    가계부 연속 미입력(신규 매수 중단) 시 발주 대상 분리
    - 보류: 신규 매수(현금성 이체·위험 축소용 단기채 교체 제외) + '매수 재원' 목적 매도·대기 현금
    - 진행: 유동성 확보 매도(Trigger A·C), 위험 축소 매도(B-1·B-2), 사용자 요청 매도, 현금성 이체
    반환: (진행 주문, 보류 주문)
    """
    if not frozen:
        return list(orders), []
    go, held = [], []
    for o in orders:
        if o.purpose == PURPOSE_FUNDING:
            held.append(o)
        elif o.side == "매수" and o.asset_class != CASH and o.purpose != PURPOSE_RISK:
            held.append(o)
        else:
            go.append(o)
    return go, held


def substitute_approval_request(subs: list, today: Optional[date] = None) -> Notification:
    total = sum(o.amount for o in subs)
    lines = ", ".join(f"{o.name} {o.quantity:,.4g}주 ≈ {won(o.amount)}" for o in subs)
    return Notification("승인 요청", f"대체 매도 승인 요청 (합계 {won(total)})",
                        f"비상금·목돈 마련 매도가 보유 수량 한도에 걸려 부족분을 다른 종목에서 팔아야 합니다: "
                        f"{lines}. 승인하시면 현재가를 다시 확인한 뒤 발주합니다.",
                        "", today or clock_today())


def _handle_substitutes(subs: list, proposal: OrderProposal, broker: BrokerAPI,
                        approve_substitutes: Optional[Callable], push: Optional[Callable],
                        today: date) -> list:
    """대체 매도: 푸시 알림 발송 → 승인 시 발주, 미응답·거절 시 승인 대기로 보관"""
    if not subs:
        return []
    n = substitute_approval_request(subs, today)
    results = [f"📲 푸시 발송: {n.title}"]
    if push:
        push(n)
    if approve_substitutes is not None and approve_substitutes(subs):
        results += ["[대체 매도 승인] " + broker.place_order(o) for o in subs]
        proposal.orders = proposal.orders + subs
    else:
        proposal.pending_substitutes = getattr(proposal, "pending_substitutes", []) + subs
        results.append("대체 매도 승인 대기 (앱 푸시에서 승인 시 execute_pending_substitutes 로 발주)")
    return results


def execute_with_approval(proposal: OrderProposal, broker: BrokerAPI,
                          approve: Callable[[OrderProposal], bool], now: datetime,
                          buy_frozen: bool = False, portfolio: Optional[Portfolio] = None,
                          approve_substitutes: Optional[Callable[[list], bool]] = None,
                          push: Optional[Callable] = None) -> list:
    """
    buy_frozen=True(가계부 연속 미입력): 신규 매수와 '매수 재원' 목적 매도는 발주하지 않고 보류
    approve_substitutes: 대체 매도 푸시 승인 결과 콜백 (None 이면 승인 대기로 보관)
    push: 푸시 알림 발송 콜백
    """
    if not proposal.orders:
        return ["주문 없음"]
    if not approve(proposal):
        return ["사용자 거절 → 발주 취소"]
    go, held = split_orders_for_ledger_freeze(proposal.orders, buy_frozen)
    results = [f"가계부 미입력으로 보류: {o.side} {o.name}"
               + (f" ({o.purpose})" if o.purpose else "") for o in held]
    now_orders = [o for o in go if o.day == 0 and (o.asset_class == CASH or is_trading_window(now))]
    later = [o for o in go if o not in now_orders]
    checked, price_held, notes, subs = pre_trade_check(now_orders, broker, portfolio)
    results += ["[발주 직전 점검] " + n for n in notes]
    for o in checked:
        if o.asset_class == CASH:
            results.append(f"계좌 이체 처리: {o.name} {won(o.amount)}")
        else:
            results.append(broker.place_order(o))
    for o in later:
        if o.day > 0:
            when = f"{_md(o.exec_date)}(T+{o.day})" if o.exec_date else f"T+{o.day}"
            results.append(f"{when} 예약 → 정산일에 발주 직전 점검(현재가·예수금) 후 발주: {o.side} {o.name}")
        else:
            results.append(f"시간대 가드(10:00~15:00 외) → 대기, 장중 발주 직전 점검 후 발주: {o.side} {o.name}")
    # 실제 체결 기준으로 제안서 갱신 (confirm 이 조정된 수량을 반영하도록)
    kept = [o for o in proposal.orders if o not in now_orders]
    proposal.orders = kept + checked
    proposal.held = getattr(proposal, "held", []) + price_held
    results += _handle_substitutes(subs, proposal, broker, approve_substitutes, push, now.date())
    return results


def execute_pending_substitutes(proposal: OrderProposal, broker: BrokerAPI, now: datetime,
                                portfolio: Optional[Portfolio] = None) -> tuple:
    """푸시로 승인된 대체 매도 발주: 현재가를 다시 점검한 뒤 발주. 반환: (결과, 발주된 주문)"""
    subs = getattr(proposal, "pending_substitutes", [])
    if not subs:
        return ["승인 대기 중인 대체 매도 없음"], []
    if not is_trading_window(now):
        return ["시간대 가드(10:00~15:00 외) → 장중에 발주"], []
    checked, held, notes, _ = pre_trade_check(subs, broker, portfolio)
    proposal.pending_substitutes = held
    results = ["[대체 매도 재점검] " + n for n in notes] + [broker.place_order(o) for o in checked]
    return results, checked


def execute_scheduled(orders: list, broker: BrokerAPI, now: datetime,
                      portfolio: Optional[Portfolio] = None,
                      approve_substitutes: Optional[Callable[[list], bool]] = None,
                      push: Optional[Callable] = None) -> tuple:
    """T+N 예약 주문을 정산일에 발주: 발주 직전 점검(현재가·예수금) 후 발주. 반환: (결과, 발주된 주문)"""
    if not is_trading_window(now):
        return [f"시간대 가드(10:00~15:00 외) → 대기: {len(orders)}건"], []
    checked, held, notes, subs = pre_trade_check(orders, broker, portfolio)
    results = ["[발주 직전 점검] " + n for n in notes]
    for o in checked:
        results.append(f"계좌 이체 처리: {o.name} {won(o.amount)}" if o.asset_class == CASH
                       else broker.place_order(o))
    tmp = OrderProposal(checked)
    results += _handle_substitutes(subs, tmp, broker, approve_substitutes, push, now.date())
    return results, tmp.orders


# ── 연 1회 정기 재평가 ─────────────────────────────────────────────
def annual_recalibration(survey: SurveyAnswers, monthly_buffers: list,
                         today: Optional[date] = None) -> Optional[RiskProfile]:
    """12개월 평균 Buffer + 재평가 시점 기준 목표까지 남은 기간으로 등급 재산출"""
    if len(monthly_buffers) < 12:
        return None
    avg = sum(monthly_buffers[-12:]) / 12
    return assess_risk(survey, avg, today)


# ════════════════════════════════════════════════════════════════════
# 트리거별 목표 비중 수정 규칙 (정식 관리 모드 · 구축 기간 공용)
# ════════════════════════════════════════════════════════════════════
class TriggerTargetMixin:
    """
    STAGE 4의 Trigger A/B/C 목표 비중 수정 규칙을 한 곳에 모은 공용 로직.
    정식 관리 모드(PortfolioManager)와 경로 A 구축 기간(BuildUpManager)이
    같은 규칙으로 목표 비중을 바꾸도록 두 클래스가 함께 상속합니다.
    """

    def _init_risk_state(self, profile: FinancialProfile, survey: SurveyAnswers):
        self.profile = profile
        self.survey = survey
        self.clock: Optional[date] = None             # 판단 기준일 (월 마감: 다음 달 1일 / 수시 스캔: 스캔일)
        self.latches: dict = {k: TriggerLatch() for k in LATCH_LABELS}
        self.b2_active = False                        # B-2 해제 전(안전자산만 매수) 여부
        self.risk = assess_risk(survey, profile.buffer, self._today())
        self.original_tier = self.risk.tier
        self.current_tier = self.risk.tier
        self.targets = self._tier_targets(self.current_tier)
        self.buffer_old = profile.buffer
        self.b2_applied_tier: Optional[int] = None
        self.b2_months = 0
        self.b1_active = False                       # B-1 Hard Stop 적용 중 여부
        self.b2_equity_rotation = False              # B-1 회복 Path 2로 등급 변경 → 주식은 비중 조정 매매만
        self.b1_floor = 0.0                          # 적용 중인 현금 하한(%)
        self.pre_b1_tier: Optional[int] = None       # B-1 직전 등급·목표 (Path 1 복귀용)
        self.pre_b1_targets: Optional[dict] = None
        self.buffer_history: list = []
        self.prev_triggers: set = set()
        self.last_emergency_balance: Optional[float] = profile.cash_current
        self.data_link = DataLink.MYDATA
        self.last_ledger_period: Optional[str] = None      # 마지막으로 입력된 가계부 월
        self.notifications: list = []                      # 발송된 알림 기록
        self.notify: Optional[Callable] = None             # 푸시 발송 콜백 (예: 앱 알림 API)
        self._sent_reminders: set = set()
        self.ledger_frozen = False                         # 가계부 연속 미입력 → 신규 매수 중단
        self._ledger_due_idx: Optional[int] = None

    def c_reserve(self, essential: float) -> float:
        return essential * self.profile.m_multiplier + self.profile.adj_debt

    def _today(self) -> date:
        return getattr(self, "clock", None) or clock_today()

    def _tier_targets(self, tier: int) -> dict:
        """등급별 목표 비중 — 생애 목표가 있으면 목표 시점까지 남은 기간으로 섞은 비중"""
        return goal_blended_targets(tier, getattr(self.survey, "goals", None), self._today())

    def _set_tier(self, tier: int, targets: Optional[dict] = None):
        self.current_tier = tier
        self.targets = targets if targets is not None else self._tier_targets(tier)

    def _is_frozen(self, snap: LedgerSnapshot, trig: set) -> bool:
        """가계부 연속 미입력, A·C 발동·해제 대기 또는 B-1 적용 중 → 위험 자산 신규 매수 전면 동결"""
        return self.ledger_frozen or bool(trig & {Trigger.A, Trigger.C}) or self.b1_active

    def _b2_safe_only(self, snap: LedgerSnapshot, trig: set) -> bool:
        """B-2 해제 전(부분 회복 전) → 주식 매수 중단, 채권·현금성 자산에만 신규 배분"""
        return getattr(self, "b2_active", False) and not self.b1_active

    # ── 트리거 진입·해제 (히스테리시스 + 최소 유지 기간 + 재진입 대기) ──
    def _latch(self, key: str) -> TriggerLatch:
        return self.__dict__.setdefault("latches", {}).setdefault(key, TriggerLatch())

    def _hold_need(self, key: str) -> int:
        """최소 유지 기간: A는 일수, B는 월 마감 횟수 (재진입 단계만큼 늘어남)"""
        steps = A_HOLD_DAYS if key == "A" else B_HOLD_MONTHS
        return steps[min(self._latch(key).level, len(steps) - 1)]

    def _latch_enter(self, key: str, log: list) -> None:
        L, today = self._latch(key), self._today()
        if L.active:
            return
        if key != "C" and L.released is not None and (today - L.released).days <= REENTRY_WINDOW_DAYS:
            old = self._hold_need(key)
            L.level = min(L.level + 1, 2)
            unit = "일" if key == "A" else "개월"
            log.append(f"[재진입 대기] {LATCH_LABELS[key]} 해제 {max(0, (today - L.released).days)}일 만에 다시 발동 → "
                       f"다음 해제의 최소 유지 기간 {old}{unit} → {self._hold_need(key)}{unit}")
        elif L.released is None or (today - L.released).days > REENTRY_WINDOW_DAYS:
            L.level = 0
        L.active, L.entered = True, today
        L.months = L.streak = L.strong = 0
        L.ok_since = None

    def _latch_release(self, key: str, log: list, why: str) -> None:
        L = self._latch(key)
        L.active, L.released, L.ok_since = False, self._today(), None
        L.months = L.streak = L.strong = 0
        log.append(f"[{LATCH_LABELS[key]} 해제] {why}")

    def _scan_triggers(self, snap: LedgerSnapshot, reserve: float, monthly: bool) -> tuple:
        """
        진입은 detect_triggers(지금과 동일), 해제는 한 걸음 더 회복 + 최소 유지 기간
        반환: (적용 중인 트리거 집합, 판단 근거 줄 목록)
          A: 잔액 ≥ 필수의 105%가 7일 연속(재진입 시 14일·30일) 또는 월 마감 확인(기본 단계만)
          B: 진입·해제는 _handle_b 에서 월 마감마다 판단 (여기서는 적용 중 여부만 표시)
          C: 대비 현금 ≥ 지출액의 105% 또는 지출일 경과 (지출 대기 현금은 지출일까지 보관)
        """
        raw = detect_triggers(snap, reserve, self.buffer_old)
        today, notes, trig = self._today(), [], set()

        la = self._latch("A")
        if Trigger.A in raw:
            self._latch_enter("A", notes)
            la.ok_since = None
        elif la.active:
            line = reserve * A_RELEASE_RATIO
            pct = snap.c_current / reserve * 100 if reserve else 0
            need = self._hold_need("A")
            if snap.c_current >= line:
                la.ok_since = la.ok_since or today
                days = (today - la.ok_since).days + 1
                if days >= need:
                    self._latch_release("A", notes, f"잔액 {won(snap.c_current)} (필수의 {pct:.0f}%) — "
                                                    f"105% 이상 {days}일 연속 유지")
                elif monthly and la.level == 0:
                    self._latch_release("A", notes, f"월 마감 확인: 잔액 {won(snap.c_current)} (필수의 {pct:.0f}%) ≥ 105%")
                else:
                    notes.append(f"[Trigger A 해제 대기] 잔액 필수의 {pct:.0f}% — 105% 이상 {days}/{need}일째"
                                 + ("" if la.level == 0 else " (재진입 단계: 월 마감 확인만으로는 해제 안 됨)"))
            else:
                la.ok_since = None
                notes.append(f"[Trigger A 유지] 잔액 필수의 {pct:.0f}% — 해제선 105%({won(line)}) 미만")
        if la.active:
            trig.add(Trigger.A)

        if Trigger.B in raw or self.b1_active or getattr(self, "b2_active", False):
            trig.add(Trigger.B)

        lc = self._latch("C")
        have = snap.c_current + snap.expense_reserved
        if Trigger.C in raw:
            self._latch_enter("C", notes)
        elif lc.active:
            passed = snap.due_date is not None and snap.due_date < (snap.as_of or today)
            if snap.upcoming_cf <= 0 or passed or (snap.dday is not None and snap.dday < 0):
                self._latch_release("C", notes, "지출일 경과")
            elif have >= snap.upcoming_cf * C_RELEASE_RATIO:
                self._latch_release("C", notes, f"대비 현금 {won(have)} ≥ 지출액 {won(snap.upcoming_cf)}의 105% "
                                                f"→ 신규 매수 재개 (확보한 지출 대기 현금은 지출일까지 보관)")
            else:
                pct = have / snap.upcoming_cf * 100 if snap.upcoming_cf else 0
                notes.append(f"[Trigger C 유지] 대비 현금 지출액의 {pct:.0f}% — 105% 확보 또는 지출일({snap.dday_label()})까지 유지")
        if lc.active:
            trig.add(Trigger.C)
        return trig, notes

    def latch_status(self, snap: LedgerSnapshot, reserve: float, today: Optional[date] = None) -> dict:
        """화면 표시용: 트리거별 단계·해제 조건·진행 상황 (상태 변경 없음)"""
        today = today or self._today()
        ratio = snap.buffer / self.buffer_old if self.buffer_old > 0 else 0.0
        la, l1, l2, lc = (self._latch(k) for k in ("A", "B1", "B2", "C"))
        a_need = self._hold_need("A")
        if la.active:
            days = (today - la.ok_since).days + 1 if la.ok_since else 0
            a = {"phase": "발동" if snap.c_current < reserve else "해제 대기",
                 "progress": f"105% 이상 {days}/{a_need}일" + (" · 월 마감 확인 시 해제" if la.level == 0 else "")}
        else:
            a = {"phase": "정상", "progress": ""}
        a["release"] = f"잔액 ≥ 필수의 105%를 {a_need}일 연속 유지" + (" (또는 월 마감 확인)" if la.level == 0 else "")
        a["level"] = la.level
        if self.b1_active:
            need = self._hold_need("B1")
            b = {"phase": "B-1", "progress": f"{l1.months}/{need}개월 · 강한 회복 {l1.strong}/{RELEASE_STREAK_MONTHS}개월",
                 "release": f"Buffer ≥ {B1_RELEASE_BUFFER:.0f}%, 최소 {need}개월 유지", "level": l1.level}
        elif getattr(self, "b2_active", False):
            need = self._hold_need("B2")
            b = {"phase": "B-2", "progress": f"{l2.months}/{need}개월 · 60% 초과 {l2.streak}/{RELEASE_STREAK_MONTHS}개월"
                                             f" · 85% 이상 {l2.strong}/{RELEASE_STREAK_MONTHS}개월",
                 "release": f"기준의 60% 초과 2개월 연속(최소 {need}개월 후) → 부분 회복, "
                            f"85% 이상 2개월 연속 → 바로 완전 복귀", "level": l2.level}
        elif self.b2_applied_tier is not None:
            b = {"phase": "B-2 부분 회복", "progress": f"85% 이상 {l2.strong}/{RELEASE_STREAK_MONTHS}개월",
                 "release": "기준의 85% 이상 2개월 연속 → 원래 등급 복귀", "level": l2.level}
        else:
            b = {"phase": "정상", "progress": "", "level": max(l1.level, l2.level),
                 "release": f"B-1 해제 Buffer ≥ {B1_RELEASE_BUFFER:.0f}% · B-2 해제 기준의 60%/85%"}
        b["ratio"] = round(ratio * 100, 1)
        c = {"phase": ("발동" if snap.upcoming_cf > snap.c_current + snap.expense_reserved else "해제 대기")
                      if lc.active else "정상",
             "progress": "", "release": "대비 현금 ≥ 지출액의 105%, 또는 지출일 경과", "level": 0}
        return {"A": a, "B": b, "C": c}

    def _log_temporary_targets(self, trig: set, log: list):
        if Trigger.C in trig:
            log.append("한시적 목표 비중(Trigger C): 장기 목표 유지 / 신규 매수 0% (Hold) / "
                       "지출 예정액만큼 현금 100% 우선 확보")
        elif Trigger.A in trig:
            log.append("한시적 목표 비중(Trigger A): 주식·채권·대체 신규 목표 0% / "
                       "신규 유입 현금 100% 비상금 계좌 배정 (Hard Freeze)")

    def _handle_a_recovery(self, snap: LedgerSnapshot, trig: set, one_off_event: bool, log: list):
        if Trigger.A in self.prev_triggers and Trigger.A not in trig:
            if one_off_event:
                log.append("[A 복귀] 일시적 지출 → 기존 목표 비중 유지")
            else:
                self.risk = assess_risk(self.survey, snap.buffer, self._today())
                self._set_tier(self.risk.tier)
                log.append(f"[A 복귀] 구조적 변화 → 등급 재산출 Tier {self.current_tier}")

    def _handle_b(self, snap: LedgerSnapshot, trig: set, log: list, monthly: bool = True):
        """
        B-1·B-2 진입·유지·해제. 처리 후 trig 의 Trigger.B 를 실제 적용 상태에 맞춰 갱신합니다.
        monthly=False(07:00 정기 업데이트·앱 실행·대형 결제 수시 스캔): B-1 진입·심화, B-2 최초 적용만 처리.
        해제(회복) 판단과 B-2 분기 점검은 한 달 치 수입·지출이 확정되는 월 마감(monthly=True)에서만.
        """
        self._handle_b_core(snap, log, monthly)
        if self.b1_active or getattr(self, "b2_active", False):
            trig.add(Trigger.B)
        else:
            trig.discard(Trigger.B)

    def _b2_partial_tier(self, ratio: float) -> tuple:
        """B-2 부분 회복 등급: 점수를 다시 계산하되 원래 등급보다 1단계 아래까지, 가능하면 적용 등급보다 1단계 위"""
        rescore = self.risk.base * (0.7 + 0.3 * min(ratio, 1.0))
        tier = min(self.original_tier - 1, max(self.b2_applied_tier + 1, score_to_tier(rescore)))
        return max(self.b2_applied_tier, tier), rescore      # 원래 등급 복귀는 85% 이상 2개월 연속일 때만

    def _b2_full_return(self, log: list, why: str) -> None:
        self._set_tier(self.original_tier)
        self.b2_applied_tier = None
        self.b2_equity_rotation = False
        log.append(f"[B-2 완전 복귀] {why} → 원래 Tier {self.current_tier}")

    def _b2_enter(self, snap: LedgerSnapshot, base_tier: int, log: list, prefix: str) -> None:
        """B-2 최초 적용 (Buffer ≥ 10%, 기준의 50% 이하)"""
        self._latch_enter("B2", log)
        self.b2_active = True
        r = handle_trigger_b2(self.risk.base, snap.buffer, self.buffer_old, base_tier)
        targets = r.targets
        if targets == MODEL_PORTFOLIOS[r.new_tier].targets:          # 일반 모델이면 생애 목표 비율도 반영
            targets = self._tier_targets(r.new_tier)
        self._set_tier(r.new_tier, targets)
        self.b2_applied_tier, self.b2_months = r.new_tier, 0
        self.profile.m_multiplier += 1
        log.append(f"{prefix} 점수 {r.new_score:.1f} → Tier {r.new_tier}: {r.note}")
        if r.new_tier != base_tier and self.pre_b1_tier is not None:
            self.b2_equity_rotation = True
            log.append(f"  기존 Tier {base_tier} → Tier {r.new_tier} 변경: 주식은 비중 조정을 위한 "
                       f"매매만 허용, 신규 현금의 주식 추가 매수 불가")

    def _handle_b_core(self, snap: LedgerSnapshot, log: list, monthly: bool):
        ratio = snap.buffer / self.buffer_old if self.buffer_old > 0 else 0.0
        l1, l2 = self._latch("B1"), self._latch("B2")
        if not hasattr(self, "b2_active"):
            self.b2_active = False

        # ── B-1 진입·심화·유지 (Buffer < 10%) ──────────────────
        if snap.buffer < 10:
            base_tier = self.pre_b1_tier if self.b1_active else self.current_tier
            r = handle_trigger_b1(snap.buffer, base_tier)
            was_active = self.b1_active
            if not self.b1_active:
                self._latch_enter("B1", log)
                self.pre_b1_tier, self.pre_b1_targets = self.current_tier, dict(self.targets)
                self.b1_active, self.b1_floor = True, r.cash_floor
                self._set_tier(r.new_tier, r.targets)
                log.append(f"[{r.kind}] Tier {r.new_tier}: {r.note}")
            elif r.cash_floor > self.b1_floor or r.new_tier < self.current_tier:
                self.b1_floor = r.cash_floor
                self._set_tier(r.new_tier, r.targets)
                log.append(f"[B-1 심화] Buffer {snap.buffer:.1f}% → {B1_PORTFOLIOS[r.new_tier].name}로 추가 하향 고정")
            else:
                log.append(f"[B-1 유지] Buffer {snap.buffer:.1f}% → {B1_PORTFOLIOS[self.current_tier].name} "
                           f"목표 비중 하향 고정 유지")
            if monthly and was_active:          # 진입한 달은 유지 기간에 넣지 않음 (B-2와 같은 기준)
                l1.months += 1
            l1.streak = l1.strong = 0
            return

        # ── B-1 해제 판단 (Buffer ≥ 12% + 최소 유지 기간, 강한 회복은 바로) ──
        if self.b1_active:
            if not monthly:
                log.append(f"[B-1 해제 대기] Buffer {snap.buffer:.1f}% — 해제 판단은 월 마감에서 "
                           f"(해제선 {B1_RELEASE_BUFFER:.0f}%)")
                return
            l1.months += 1
            ok = snap.buffer >= B1_RELEASE_BUFFER
            l1.streak = l1.streak + 1 if ok else 0
            l1.strong = l1.strong + 1 if ok and ratio >= B2_FULL_RATIO else 0
            need = self._hold_need("B1")
            strong = l1.strong >= RELEASE_STREAK_MONTHS
            if not (ok and (l1.months >= need or strong)):
                why = (f"해제선 {B1_RELEASE_BUFFER:.0f}% 미만" if not ok else f"최소 유지 {l1.months}/{need}개월")
                log.append(f"[B-1 유지] Buffer {snap.buffer:.1f}% — {why} · 강한 회복 {l1.strong}/"
                           f"{RELEASE_STREAK_MONTHS}개월 → {B1_PORTFOLIOS[self.current_tier].name} 유지")
                return
            self._latch_release("B1", log, f"Buffer {snap.buffer:.1f}% ≥ {B1_RELEASE_BUFFER:.0f}% · "
                                           + (f"강한 회복 {l1.strong}개월 연속 (최소 유지 기간 {need}개월 전 조기 해제)"
                                              if strong and l1.months < need else f"{l1.months}개월 유지"))
            self.b1_active, self.b1_floor = False, 0.0
            if ratio > B2_ENTRY_RATIO:
                # Path 1: 기준의 50% 초과 → 동결 완전 해제, B-1 직전 등급·목표 복귀 (B-2 적용 중이었다면 B-2 상태 유지)
                self._set_tier(self.pre_b1_tier, self.pre_b1_targets)
                log.append(f"[B-1 회복 Path 1] 기준의 {ratio * 100:.0f}% → 신규 매수 동결 해제, "
                           f"기존 Tier {self.current_tier} 목표 비중 복귀")
            elif self.b2_applied_tier is not None:
                b1_tier = self.current_tier
                self._set_tier(self.pre_b1_tier, self.pre_b1_targets)
                if self.current_tier != b1_tier:
                    self.b2_equity_rotation = True
                log.append(f"[B-1 회복 Path 2] 기준의 {ratio * 100:.0f}% → 매수 동결 해제, "
                           f"기존 B-2 Tier {self.current_tier} 유지")
            else:
                base = self.pre_b1_tier
                self._b2_enter(snap, base, log, f"[B-1 회복 Path 2 → B-2 적용] 기준의 {ratio * 100:.0f}% →")
            self.pre_b1_tier = self.pre_b1_targets = None
            return

        # ── B-2 진입·유지 (Buffer ≤ 기준의 50%) ────────────────
        if self.buffer_old > 0 and ratio <= B2_ENTRY_RATIO:
            if not self.b2_active:
                if self.b2_applied_tier is None:
                    self._b2_enter(snap, self.current_tier, log, "[B-2 Soft Adjust]")
                else:
                    # 부분 회복 상태에서 다시 50% 이하 → 부분 회복분을 되돌리고 B-2 재적용
                    self._latch_enter("B2", log)
                    self.b2_active = True
                    self._set_tier(self.b2_applied_tier)
                    self.b2_months = 0
                    log.append(f"[B-2 재적용] 기준의 {ratio * 100:.0f}% → Tier {self.current_tier}로 다시 하향, "
                               f"주식 매수 중단·안전자산 희석")
            elif not monthly:
                log.append(f"[B-2 적용 중] Tier {self.current_tier} 유지 (해제·분기 점검은 월 마감에서)")
            else:
                l2.months += 1
                l2.streak = l2.strong = 0
                self.b2_months += 1
                t = b2_quarterly_review(self.b2_applied_tier, self.b2_months, snap.buffer, self.buffer_old)
                if t != self.b2_applied_tier:
                    self.b2_applied_tier = t
                    self._set_tier(t)
                    self.b2_months = 0
                    log.append(f"[B-2 분기 점검] 미회복 → Tier {t}로 추가 하향")
                else:
                    log.append(f"[B-2 유지] 기준의 {ratio * 100:.0f}% — 해제선 60% 이하 "
                               f"({l2.months}/{self._hold_need('B2')}개월)")
            return

        # ── B-2 해제 판단 (기준의 50% 초과, 월 마감에서만) ────────
        if self.b2_active:
            if not monthly:
                log.append(f"[B-2 해제 대기] 기준의 {ratio * 100:.0f}% — 해제 판단은 월 마감에서")
                return
            l2.months += 1
            self.b2_months += 1
            l2.streak = l2.streak + 1 if ratio > B2_PARTIAL_RATIO else 0
            l2.strong = l2.strong + 1 if ratio >= B2_FULL_RATIO else 0
            need = self._hold_need("B2")
            if l2.strong >= RELEASE_STREAK_MONTHS:
                early = l2.months < need
                self._latch_release("B2", log, f"기준의 85% 이상 {l2.strong}개월 연속"
                                               + (f" — 강한 회복 (최소 유지 {need}개월 전 조기 해제)" if early else ""))
                self.b2_active = False
                self._b2_full_return(log, f"Buffer 기준의 {ratio * 100:.0f}%")
            elif l2.months >= need and l2.streak >= RELEASE_STREAK_MONTHS:
                self._latch_release("B2", log, f"기준의 60% 초과 {l2.streak}개월 연속 · {l2.months}개월 유지")
                self.b2_active = False
                l2.strong = 1 if ratio >= B2_FULL_RATIO else 0      # 완전 복귀 연속 판단은 이어서
                tier, rescore = self._b2_partial_tier(ratio)
                self._set_tier(tier)
                log.append(f"[B-2 부분 회복] 재계산 점수 {rescore:.1f} → Tier {tier} (안전자산 전용 매수 해제, "
                           f"원래 Tier {self.original_tier} 복귀는 기준의 85% 이상 2개월 연속일 때)")
            else:
                log.append(f"[B-2 유지] 기준의 {ratio * 100:.0f}% — 최소 유지 {l2.months}/{need}개월 · "
                           f"60% 초과 {l2.streak}/{RELEASE_STREAK_MONTHS}개월 · 85% 이상 {l2.strong}/"
                           f"{RELEASE_STREAK_MONTHS}개월")
            return

        # ── B-2 부분 회복 상태 → 완전 복귀 판단 ──────────────────
        if self.b2_applied_tier is not None and monthly:
            l2.strong = l2.strong + 1 if ratio >= B2_FULL_RATIO else 0
            if l2.strong >= RELEASE_STREAK_MONTHS:
                self._b2_full_return(log, f"기준의 85% 이상 {l2.strong}개월 연속")
                l2.strong = 0
            elif ratio > B2_PARTIAL_RATIO:
                tier, rescore = self._b2_partial_tier(ratio)
                if tier > self.current_tier:
                    self._set_tier(tier)
                    log.append(f"[B-2 부분 회복] 재계산 점수 {rescore:.1f} → Tier {tier}")
                else:
                    log.append(f"[B-2 부분 회복 유지] Tier {self.current_tier} · 85% 이상 {l2.strong}/"
                               f"{RELEASE_STREAK_MONTHS}개월")
            else:
                log.append(f"[B-2 부분 회복 유지] 기준의 {ratio * 100:.0f}% — 50% 이하로 떨어지기 전까지 Tier "
                           f"{self.current_tier} 유지")

    def _b1_hold_only(self, trig: set) -> bool:
        """B-1만 적용 중(A·C 없음): 보유 자산(수익권 포함) 매도 없이 현금만 적립"""
        return self.b1_active and not (trig & {Trigger.A, Trigger.C})

    def _equity_rotation_args(self, sells: list, deficits: dict) -> dict:
        """Path 2 주식 비중 조정: 주식 매도 대금 한도 안에서만 주식 매수"""
        if not self.b2_equity_rotation:
            return {}
        return dict(equity_budget=sum(o.amount for o in sells if o.asset_class in EQUITY_CLASSES),
                    equity_deficits={c: a for c, a in deficits.items() if c in EQUITY_CLASSES})

    def _overseas_ytd(self) -> float:
        st = getattr(self, "state", None)
        if st is not None:
            return st.realized_overseas_net
        return getattr(self, "realized_overseas_net", getattr(self, "realized_overseas_gain_ytd", 0.0))

    def _b1_adjust_orders(self, trig: set, log: list) -> tuple:
        """
        B-1 적용 중 보유 자산 매도는 'B-1 등급 변동에 따른 비중 조정'만 허용.
        - 기준: B-1 Tier 2(주식10/단기채40/현금50) 또는 B-1 Tier 1(단기채30/현금70)
          (B-1 등급은 일반 등급과 별도 포트폴리오이므로 B-1 진입·심화 자체가 등급 변동)
        ① 위험 자산(주식·대체·고위험채·암호화폐) 초과분 → 수익권만 50%씩 매도 → 현금
        ② 채권 구성 → 만기 3개월 미만 단기채 위주로 교체
           장기채(만기 3개월 이상·미입력)는 수익권만 보유액의 50%씩 매도,
           대금은 단기채 목표 부족분만큼 단기채 매수, 나머지는 현금
        - 손실 종목은 회복 시까지 보류, 그 외 이유의 매도는 불가
        반환: (주문 목록, 해외 실현 손익)
        """
        if not self._b1_hold_only(trig) or self.pre_b1_tier is None:
            return [], 0.0
        name_ = B1_PORTFOLIOS[self.current_tier].name
        log.append(f"[B-1] 기존 Tier {self.pre_b1_tier} → {name_}: 등급 변동에 따른 비중 조정 매도만 허용")
        ticker, cname = _cash_ticker(self.instruments)

        # ① 위험 자산 비중 조정
        sells, notes, net = b2_gradual_exit(
            self.portfolio, self.targets,
            tax_room=max(0.0, OVERSEAS_TAX_FREE_LIMIT - self._overseas_ytd()),
            label="B-1 등급 변동", keep_classes=(IG_BOND, CASH))
        log += notes
        orders = list(sells)
        to_cash = sum(o.amount for o in sells)
        day = max((self.portfolio.find(o.ticker).settlement_days for o in sells), default=0)

        # ② 채권 구성: 장기채 → 단기채(만기 3개월 미만)
        total = self.portfolio.total()
        bonds = [h for h in self.portfolio.holdings if h.asset_class == IG_BOND and not h.locked]
        short_val = sum(h.value for h in bonds if is_short_bond(h))
        longs = [h for h in bonds if not is_short_bond(h)]
        long_sell = 0.0
        held = [h.name for h in longs if h.profit_pct < 0]
        if held:
            log.append(f"B-1 채권 교체 보류(손실 중): {', '.join(held)} → 수익권 회복 시 단기채로 교체")
        for h in sorted([h for h in longs if h.profit_pct >= 0], key=lambda h: -h.profit_pct):
            o = _sell_order(h, h.value * B2_EXIT_RATIO, 0,
                            f"B-1 장기채 → 단기채 교체 매도 (보유액 {int(B2_EXIT_RATIO * 100)}%, "
                            f"만기 {h.maturity_months if h.maturity_months is not None else '미입력'}개월)",
                            round_up=False, purpose=PURPOSE_RISK)
            if o:
                orders.append(o)
                long_sell += o.amount
                day = max(day, h.settlement_days)
        if long_sell > 0:
            short_need = max(0.0, total * self.targets[IG_BOND] / 100 - short_val)
            inst = self.instruments.get(SHORT_BOND_KEY)
            short_amt = min(long_sell, short_need)
            if inst and short_amt >= inst.price:
                qty = math.floor(short_amt / inst.price)
                orders.append(Order("매수", inst.ticker, inst.name, IG_BOND, qty, inst.price, day,
                                    "B-1 단기채(만기 3개월 미만) 편입", PURPOSE_RISK))
                to_cash += long_sell - qty * inst.price
                log.append(f"[B-1] 장기채 {won(long_sell)} 매도 → 단기채 {won(qty * inst.price)} 편입, "
                           f"나머지 현금")
            else:
                to_cash += long_sell
                if inst is None:
                    log.append("[B-1] 단기채 대표 종목 미지정 → 장기채 매도 대금은 현금 보관")

        if not orders:
            log.append("[B-1] 비중 조정 대상(초과·수익권) 없음 → 매도 없이 현금만 적립")
            return [], 0.0
        if to_cash > 0.5:
            orders.append(Order("매수", ticker, cname, CASH, to_cash, 1.0, day,
                                "B-1 비중 조정 매도 대금 → 현금 확보", PURPOSE_RISK))
            log.append(f"[B-1] 비중 조정 매도 대금 중 {won(to_cash)} → 현금성 자산 최우선 확보")
        return orders, net

    def _b1_cash_orders(self, snap: LedgerSnapshot, trig: set, log: list) -> list:
        """B-1 적용 중(A·C 없음): 가계부 잉여금을 현금성 자산에 최우선 적립"""
        if not self.b1_active or trig & {Trigger.A, Trigger.C} or snap.free_cash <= 0:
            return []
        ticker, name = _cash_ticker(self.instruments)
        log.append(f"[B-1] 가계부 잉여금 {won(snap.free_cash)} → 현금성 자산 최우선 적립")
        return [Order("매수", ticker, name, CASH, snap.free_cash, 1.0, 0, "B-1 현금 비중 최우선 확보")]

    def to_manager(self) -> "PortfolioManager":
        """구축 완료 → 정식 관리 모드로 상태 그대로 이관"""
        m = PortfolioManager(self.profile, self.survey, self.portfolio, self.instruments,
                             data_link=self.data_link)
        for attr in ("risk", "original_tier", "current_tier", "targets", "buffer_old",
                     "b2_applied_tier", "b2_months", "buffer_history", "prev_triggers",
                     "b1_active", "b1_floor", "pre_b1_tier", "pre_b1_targets", "b2_equity_rotation",
                     "last_emergency_balance", "last_ledger_period", "notify", "notifications",
                     "_sent_reminders", "ledger_frozen", "_ledger_due_idx",
                     "clock", "latches", "b2_active"):
            setattr(m, attr, getattr(self, attr))
        # 올해 해외주식 실현 손익(손익 상계·비과세 한도용)도 이어받음
        st = getattr(self, "state", None)
        m.realized_overseas_net = (st.realized_overseas_net if st is not None
                                   else getattr(self, "realized_overseas_gain_ytd", 0.0))
        return m

    def _resolve_snapshot(self, snap: LedgerSnapshot) -> LedgerSnapshot:
        """
        비상금 계좌 잔액 확정
        - 잔액 미입력: 지난달 잔액 + 입금 − 출금 + 지난달 시스템 이체액
        - 잔액 직접 입력: 입력값 사용 (시스템 이체액은 이미 반영된 것으로 간주)
        """
        snap = copy.copy(snap)
        # 판단 기준일
        #   monthly_cycle(today=...) 로 받은 실제 마감일 (웹 서비스: 오늘 — 월말 전에 미리 마감해도 미래로 가지 않음)
        #   없으면 가계부 월의 마감일(다음 달 1일), 월 정보도 없으면 한 달씩 전진 (시뮬레이션·데모)
        close_today = getattr(self, "_close_today", None)
        if close_today is not None:
            self.clock = close_today
        elif snap.period:
            y, m = int(snap.period[:4]), int(snap.period[5:7])
            self.clock = date(y + (m == 12), m % 12 + 1, 1)
        else:
            self.clock = (getattr(self, "clock", None) or clock_today()) + timedelta(days=30)
        if snap.as_of is None:                      # 매도 주문일 (정산일 계산 기준)
            snap.as_of = self.clock
        transfer = getattr(self, "pending_emergency_transfer", 0.0)
        self.pending_emergency_transfer = 0.0
        self._balance_entered = snap.emergency_balance is not None
        snap.system_transfer = transfer
        if snap.emergency_balance is None:
            last = getattr(self, "last_emergency_balance", None)
            if last is None:
                raise ValueError("첫 달은 비상금 계좌 잔액을 입력해 주세요.")
            snap.emergency_balance = last + snap.emergency_net_flow + transfer
        self.last_emergency_balance = snap.emergency_balance
        if snap.period and (self.last_ledger_period is None or
                            _period_index(snap.period) > _period_index(self.last_ledger_period)):
            self.last_ledger_period = snap.period
        # 가장 최근 마감 대상 월까지 입력되면 매수 중단 해제
        if (self.ledger_frozen and self.last_ledger_period and self._ledger_due_idx is not None
                and _period_index(self.last_ledger_period) >= self._ledger_due_idx):
            self.ledger_frozen = False
            n = Notification("해제", "가계부 입력 확인 → 신규 매수 재개",
                             f"{self.last_ledger_period} 가계부까지 입력되어 트리거 감시와 신규 매수를 재개합니다.",
                             self.last_ledger_period, self._today())
            self.notifications.append(n)
            if self.notify:
                self.notify(n)
        return snap

    def _executable(self, proposal: OrderProposal) -> list:
        """승인 후 실제로 진행되는 주문 (가계부 미입력 보류분 제외)"""
        return split_orders_for_ledger_freeze(proposal.orders, self.ledger_frozen)[0]

    def sync_holdings(self, api: BrokerDataAPI) -> list:
        """증권사 API로 보유 종목 동기화 (마이데이터·직접 입력 사용자 공통)"""
        self.portfolio, notes = sync_holdings(self.portfolio, api)
        return notes

    @property
    def buy_frozen(self) -> bool:
        """발주 단계 매수 보류 여부 (execute_with_approval 의 buy_frozen 인자로 전달)"""
        return self.ledger_frozen

    def check_ledger_input(self, today: date) -> list:
        """
        직접 입력 사용자: 가계부 미입력 여부 확인 후 알림 발송 (매일 1회 호출 가정)
        마감이 지난 상태로 2개월 이상 연속 미입력이면 신규 매수 중단(ledger_frozen)
        """
        if _as_data_link(self.data_link) == DataLink.MANUAL:
            due_idx, overdue, missed = ledger_status(self.last_ledger_period, today)
            self._ledger_due_idx = due_idx
            if overdue and missed >= LEDGER_FREEZE_MONTHS:
                self.ledger_frozen = True
        notes = ledger_reminders(self.data_link, self.last_ledger_period, today, self._sent_reminders)
        for n in notes:
            self.notifications.append(n)
            if self.notify:
                self.notify(n)
        return notes

    def _plan_emergency_transfer(self, amount: float, log: list) -> None:
        """Trigger A 대응으로 비상금 계좌에 이체할 금액 예약 (승인·체결 시 확정)"""
        self._planned_emergency_transfer = getattr(self, "_planned_emergency_transfer", 0.0) + max(0.0, amount)
        if amount > 0.5:
            log.append(f"[비상금 계좌] 시스템 이체 예정 {won(amount)} → 다음 달 잔액에 자동 반영")

    def _commit_emergency_transfer(self) -> float:
        amt = getattr(self, "_planned_emergency_transfer", 0.0)
        self.pending_emergency_transfer = getattr(self, "pending_emergency_transfer", 0.0) + amt
        self._planned_emergency_transfer = 0.0
        return amt

    def _a_transfer_amount(self, snap: LedgerSnapshot, sell_orders: list, extra: float = 0.0) -> float:
        """Trigger A: 신규 유입 현금(잉여금) 100% + 비상금 충당 매도 대금 + 기타 이체액"""
        return max(0.0, snap.free_cash) + sum(o.amount for o in sell_orders if o.side == "매도") + extra

    def _header(self, snap: LedgerSnapshot, reserve: float, trig: set) -> list:
        parts = []
        linked = snap.balance_source.startswith(BALANCE_SOURCE_MYDATA)
        if snap.balance_source and (linked or "사용자 수정" in snap.balance_source
                                    or "오프라인" in snap.balance_source):
            parts.append(snap.balance_source)
        if snap.emergency_deposit or snap.emergency_withdrawal:
            ref = "참고: " if linked else ""
            parts.append(f"{ref}입금 +{won(snap.emergency_deposit)} / 출금 −{won(snap.emergency_withdrawal)}")
        if snap.system_transfer:
            if linked:
                parts.append(f"시스템 이체 {won(snap.system_transfer)}는 연동 잔액에 이미 반영")
            elif getattr(self, "_balance_entered", False):
                parts.append(f"직접 입력 잔액에 시스템 이체 {won(snap.system_transfer)} 포함 간주")
            else:
                parts.append(f"시스템 이체 +{won(snap.system_transfer)}")
        flow = f" ({' / '.join(parts)})" if parts else ""
        pre = ["⛔ 가계부 연속 미입력 → 신규 매수 중단 중 (최근 마감 월까지 입력 시 재개)"] if self.ledger_frozen else []
        return pre + [f"필수 비상금 {won(reserve)} / 비상금 계좌 잔액 {won(snap.c_current)}{flow} / "
                f"Buffer {snap.buffer:.1f}% (기준 {self.buffer_old:.1f}%)",
                "적용 중 트리거(해제 대기 포함): " + (", ".join(t.value for t in trig) if trig else "없음")]


# ════════════════════════════════════════════════════════════════════
# STAGE 3 - 경로 A. 신규 투자자 빌드업 (3회 분할 매수)
# ════════════════════════════════════════════════════════════════════
DCA_ROUNDS = 3   # 분할 매수 횟수 (고정)


class BuildUpManager(TriggerTargetMixin):
    """
    신규 투자자 포트폴리오 구축 기간 관리.
    - 보유 현금 - 필수 비상금 = 투자 대기 현금(pending_cash)
    - 3회 분할 매수, 회차별 금액 = 대기 현금 / 남은 회차
    - 구축 중 Trigger A/B/C 발생 시 STAGE 4와 동일한 규칙으로 목표 비중 수정
    - 배정액이 1주 가격 미만이면 매수 유예 → 현금 자산(CMA)으로 흡수,
      다음 회차에 모이면 다시 투입
    snap.c_current 는 투자 대기 현금을 제외한 비상금 계좌 등 현금성 자산입니다.
    """

    def __init__(self, profile: FinancialProfile, survey: SurveyAnswers, instruments: dict,
                 data_link=DataLink.MYDATA):
        self._init_risk_state(profile, survey)
        self.instruments = instruments
        self.data_link = _as_data_link(data_link)
        self.completed = False          # 정식 관리 모드 전환 가능 여부 (3중 검증)
        self._last_trig: set = set()
        self.n_rounds = DCA_ROUNDS
        self.pending_cash = profile.cash_current - profile.c_reserve
        if self.pending_cash <= 0:
            raise ValueError(f"보유 현금 {won(profile.cash_current)}이 필수 비상금 "
                             f"{won(profile.c_reserve)} 이하입니다. 비상금 확보가 우선입니다.")
        self.portfolio = Portfolio()
        self.executed_rounds = 0
        self.last_emergency_balance = profile.c_reserve   # 투자 대기 현금을 뺀 비상금 계좌
        self._planned_budget = 0.0

    @property
    def remaining_rounds(self) -> int:
        return self.n_rounds - self.executed_rounds

    @property
    def rounds_done(self) -> bool:
        return self.remaining_rounds <= 0

    # ── 가계부 이벤트 ─────────────────────────────────────────────
    def add_income(self, surplus: float) -> None:
        """가계부 잉여금 → 다음 회차 매수 예정금에 합산"""
        if surplus > 0:
            self.pending_cash += surplus

    def absorb_expense(self, amount: float) -> float:
        """갑작스러운 지출 → 미집행 대기 현금에서 우선 차감. 못 막은 금액 반환"""
        used = min(self.pending_cash, amount)
        self.pending_cash -= used
        return amount - used

    # ── 회차 매수 주문 생성 ───────────────────────────────────────
    def _round_orders(self, budget: float, safe_only: bool) -> tuple:
        cv = self.portfolio.class_values()
        total_after = self.portfolio.total() + budget
        desired = {c: self.targets.get(c, 0) / 100 * total_after for c in ASSET_CLASSES}
        allowed = (IG_BOND, CASH) if safe_only else tuple(ASSET_CLASSES)
        weights = {c: max(0.0, desired[c] - cv[c]) for c in allowed if c != CASH}
        weights = {c: w for c, w in weights.items() if w > 0}

        if not weights:  # 살 자산이 없으면 전액 현금 자산으로
            co = _cash_order(budget, self.instruments, 0, "매수 대상 없음 → 현금 자산 흡수")
            return ([co] if co else []), []

        # 이전 회차에서 유예·흡수되어 목표를 넘은 현금은 재투입
        excess_cash = max(0.0, cv[CASH] - desired[CASH])
        cash_share = max(0.0, desired[CASH] - cv[CASH])
        if cash_share > 0:
            weights[CASH] = cash_share
        orders, notes = allocate_buys(budget + excess_cash, weights, self.instruments, 0,
                                      f"{self.executed_rounds + 1}회차 분할 매수")
        # 현금 입출금을 한 건으로 정리
        cash_in = sum(o.amount for o in orders if o.asset_class == CASH)
        orders = [o for o in orders if o.asset_class != CASH]
        net = cash_in - excess_cash
        inst = self.instruments.get(CASH)
        ticker, name = (inst.ticker, inst.name) if inst else ("CMA", "CMA/파킹통장")
        if net > 0.5:
            orders.append(Order("매수", ticker, name, CASH, net, 1.0, 0,
                                "매수 유예·자투리·현금 비중 → 현금 자산 흡수"))
        elif net < -0.5:
            orders.append(Order("매도", ticker, name, CASH, -net, 1.0, 0, "유예됐던 현금 재투입"))
        return orders, notes

    # ── 월간 구축 루프 ────────────────────────────────────────────
    def monthly_step(self, snap: LedgerSnapshot, one_off_event: bool = True) -> tuple:
        snap = self._resolve_snapshot(snap)
        log, orders = [], []
        self._planned_budget = 0.0
        self.buffer_history.append(snap.buffer)
        reserve = self.c_reserve(snap.essential_expense)
        trig, hold_notes = self._scan_triggers(snap, reserve, monthly=True)
        log += self._header(snap, reserve, trig) + hold_notes
        log.append(f"구축 진행: {self.executed_rounds}/{self.n_rounds}회 완료, "
                   f"투자 대기 현금 {won(self.pending_cash)}")
        self._log_temporary_targets(trig, log)

        # Trigger C: 대기 현금 → 지출 대기 현금 우선 전환, 부족분만 보유 자산 현금화
        if Trigger.C in trig and snap.upcoming_cf - snap.c_current <= 0:
            log.append("[Trigger C] 해제 대기 — 지출 자금 확보됨, 추가 현금화 없이 구축 매수 유예 유지")
        elif Trigger.C in trig:
            shortage = snap.upcoming_cf - snap.c_current
            moved = min(self.pending_cash, shortage)
            self.pending_cash -= moved
            log.append(f"[Trigger C] 부족액 {won(shortage)} → 투자 대기 현금 {won(moved)} 지출 대기로 전환")
            rest = shortage - moved
            if rest > 0 and self.portfolio.holdings:
                adj = copy.copy(snap)
                adj.c_current = snap.c_current + moved
                plan = handle_trigger_c(adj, self.portfolio, self.targets, self._overseas_ytd())
                orders += plan.orders
                log.append(f"  남은 {won(rest)}은 매도 점수(Score_i) 순으로 현금화")
                if plan.uncovered > 0:
                    log.append(f"  ⚠ D-Day 내 정산 가능한 자산으로 {won(plan.uncovered)} 부족")

        # Trigger A: 대기 현금 → 비상금 우선 충전, 부족분만 A-1/A-2 판단
        if Trigger.A in trig and Trigger.C not in trig and snap.c_current >= reserve:
            log.append("[Trigger A] 해제 대기 — 추가 충전 없이 구축 일시 중단, 잉여금은 비상금 계좌로")
            self._plan_emergency_transfer(self._a_transfer_amount(snap, []), log)
        elif Trigger.A in trig and Trigger.C not in trig:
            shortage = reserve - snap.c_current
            moved = min(self.pending_cash, shortage)
            self.pending_cash -= moved
            log.append(f"[Trigger A] 부족액 {won(shortage)} → 투자 대기 현금 {won(moved)} 비상금 계좌로 충전")
            rest = shortage - moved
            a_sells = []
            if rest > 0:
                adj = copy.copy(snap)
                adj.c_current = snap.c_current + moved
                plan = handle_trigger_a(adj, reserve, self.portfolio, self.targets)
                orders += plan.orders
                a_sells = plan.orders
                log.append(f"  남은 {won(rest)} → {plan.mode}: {plan.note}")
            self._plan_emergency_transfer(self._a_transfer_amount(snap, a_sells, moved), log)

        self._handle_a_recovery(snap, trig, one_off_event, log)
        self._handle_b(snap, trig, log)

        if self._is_frozen(snap, trig):
            if self.rounds_done:
                log.append("분할 매수 완료, 트리거 발동 중 → 정식 관리 모드 전환 대기")
            else:
                log.append(f"구축 일시 중단 → {self.executed_rounds + 1}회차 매수 보류 (회차 소진 없음)")
            if self.portfolio.holdings:
                b1_orders, _ = self._b1_adjust_orders(trig, log)
                orders += b1_orders
            if self.b1_active and not (trig & {Trigger.A, Trigger.C}) and snap.free_cash > 0:
                self.add_income(snap.free_cash)
                log.append(f"[B-1] 가계부 잉여금 {won(snap.free_cash)} → 현금(투자 대기)으로 최우선 적립")
        elif self.rounds_done:
            log.append("분할 매수 3회 완료 → 전환 검증 대기")
            leftover = self.pending_cash + max(0.0, snap.free_cash)
            if leftover > 0.5:     # 트리거 기간에 쌓인 대기 현금 + 이번 달 잉여금 → 목표 비중대로 투입
                o, n = self._round_orders(leftover, self._b2_safe_only(snap, trig))
                orders += o
                log += n
                self._planned_budget = leftover
                self._leftover_round = True
                log.append(f"잔여 대기 현금·잉여금 {won(leftover)} 목표 비중대로 투입")
        else:
            if snap.free_cash > 0:
                self.add_income(snap.free_cash)
                log.append(f"가계부 잉여금 {won(snap.free_cash)} → 이번 회차 매수금에 합산")
            budget = self.pending_cash / self.remaining_rounds
            safe_only = self._b2_safe_only(snap, trig)
            if safe_only:
                log.append("B-2 적용 중 → 이번 회차는 채권·현금성 자산만 매수")
            o, n = self._round_orders(budget, safe_only)
            orders += o
            log += n
            self._planned_budget = budget
            log.append(f"{self.executed_rounds + 1}회차 매수금 {won(budget)} (목표: {self.targets_label()})")

        self.prev_triggers = trig
        self._last_trig = trig
        return log, OrderProposal(orders, "구축 기간 매매 제안")

    def confirm(self, proposal: OrderProposal) -> str:
        """[매수 완료] 확인 → 체결 반영, 회차 소진, 비상금 계좌 이체 확정, 전환 검증"""
        self.portfolio = self.portfolio.apply(self._executable(proposal), self.instruments)
        self._commit_emergency_transfer()
        if self._planned_budget > 0:
            if getattr(self, "_leftover_round", False):
                self.pending_cash = 0.0          # 잔여 대기 현금 투입 (회차 아님)
                self._leftover_round = False
            else:
                self.pending_cash = max(0.0, self.pending_cash - self._planned_budget)
                self.executed_rounds += 1
            self._planned_budget = 0.0
        ok, msg = buildup_transition_ready(self.rounds_done, self._last_trig, self.data_link)
        self.completed = ok
        return msg

    def targets_label(self) -> str:
        return ", ".join(f"{c} {w:.0f}%" for c, w in self.targets.items() if w > 0)

# ════════════════════════════════════════════════════════════════════
# STAGE 3 - 경로 B / 전략 A 전환 관리 (트리거 대응)
# ════════════════════════════════════════════════════════════════════
class StrategyAManager(TriggerTargetMixin):
    """
    전략 A(즉시 리밸런싱) 전환 기간 관리.
    전환 도중 Trigger A/B/C가 발생하면 STAGE 4와 같은 규칙으로 목표 비중을 수정합니다.
      - A·C·B-1: 매수 동결, 매도 대금은 부족 현금에 우선 사용 후 현금 대기
      - B-2    : 하향된 등급으로 목표 재설정, 채권·현금성 자산만 매수
    트리거 해제 후 다음 회차에 현금 대기분까지 포함해 다시 일괄 정렬합니다.
    """

    def __init__(self, profile: FinancialProfile, survey: SurveyAnswers, portfolio: Portfolio,
                 instruments: dict, data_link=DataLink.MYDATA, realized_overseas_gain_ytd: float = 0.0):
        self._init_risk_state(profile, survey)
        self.portfolio = portfolio
        self.instruments = instruments
        self.data_link = _as_data_link(data_link)
        self.realized_overseas_gain_ytd = realized_overseas_gain_ytd
        self.days_elapsed = 0
        self.completed = False
        self._last_plan: Optional[RestructuringPlan] = None
        self._last_trig: set = set()

    def step(self, snap: LedgerSnapshot, one_off_event: bool = True, days_passed: int = 30) -> tuple:
        snap = self._resolve_snapshot(snap)
        log, orders = [], []
        self.days_elapsed += days_passed
        self.buffer_history.append(snap.buffer)
        reserve = self.c_reserve(snap.essential_expense)
        trig, hold_notes = self._scan_triggers(snap, reserve, monthly=True)
        log += self._header(snap, reserve, trig) + hold_notes
        self._log_temporary_targets(trig, log)
        self._handle_a_recovery(snap, trig, one_off_event, log)
        self._handle_b(snap, trig, log)

        need = 0.0
        if Trigger.C in trig:
            need = max(0.0, snap.upcoming_cf - snap.c_current)
            log.append(f"[Trigger C] 부족액 {won(need)} → 매도 대금 우선 충당, 신규 매수 유예")
        elif Trigger.A in trig:
            need = max(0.0, reserve - snap.c_current)
            log.append(f"[Trigger A] 부족액 {won(need)} → 매도 대금 우선 충당, 신규 매수 동결")

        if self._b1_hold_only(trig):
            log.append("[B-1] 전환 매매 일시 중지: 등급 변동 비중 조정 외 보유 자산 매도 없음")
            b1_orders, net = self._b1_adjust_orders(trig, log)
            orders += b1_orders
            self.realized_overseas_gain_ytd += net
            orders += self._b1_cash_orders(snap, trig, log)
            self._last_plan, self._last_trig = None, trig
            self.prev_triggers = trig
            return log, OrderProposal(orders, "전략 A 주문서 (B-1)")

        plan = restructuring_orders(
            self.portfolio, self.targets, self.instruments,
            hold_buys=self._is_frozen(snap, trig), safe_only=self._b2_safe_only(snap, trig),
            cash_need=need, realized_overseas_gain_ytd=self.realized_overseas_gain_ytd,
            equity_rotation=self.b2_equity_rotation,
            sell_deadline_days=snap.deadline() if Trigger.C in trig else None)
        orders += plan.orders
        log += plan.notes

        # 매도 대금으로 부족 현금을 못 채우면 STAGE 4 방식으로 추가 현금화
        a_extra = []
        if plan.uncovered_need > 0:
            after_sells = self.portfolio.apply(plan.sell_orders, self.instruments)
            adj = copy.copy(snap)
            adj.c_current = snap.c_current + plan.withdrawn
            if Trigger.C in trig:
                extra = handle_trigger_c(adj, after_sells, self.targets, self._overseas_ytd())
                orders += extra.orders
                log.append(f"  남은 {won(plan.uncovered_need)} → 매도 점수(Score_i) 순 추가 현금화")
            else:
                extra = handle_trigger_a(adj, reserve, after_sells, self.targets)
                orders += extra.orders
                a_extra = extra.orders
                log.append(f"  남은 {won(plan.uncovered_need)} → {extra.mode}: {extra.note}")
        if Trigger.A in trig and Trigger.C not in trig:
            self._plan_emergency_transfer(self._a_transfer_amount(snap, a_extra, plan.withdrawn), log)

        self._last_plan, self._last_trig = plan, trig
        self.prev_triggers = trig
        return log, OrderProposal(orders, "전략 A 일괄 교체 주문서", extra=plan.cost.lines())

    def confirm(self, proposal: OrderProposal) -> str:
        """승인·체결 반영 후 전환 완료(3중 검증) 판정"""
        before = self.portfolio
        self.portfolio = self.portfolio.apply(self._executable(proposal), self.instruments)
        self._commit_emergency_transfer()
        for o in self._executable(proposal):
            h = before.find(o.ticker)
            if o.side == "매도" and h:
                self.realized_overseas_gain_ytd += _overseas_gain(h, o.amount)
        adj = locked_adjusted_targets(self.portfolio, self.targets)
        ok, msg = transition_ready(self.portfolio, adj, "A", self._last_trig,
                                   self.data_link, self.days_elapsed)
        self.completed = ok
        return msg


# ════════════════════════════════════════════════════════════════════
# STAGE 3 - 경로 B / 전략 B 전환 관리 (트리거 대응)
# ════════════════════════════════════════════════════════════════════
class StrategyBManager(TriggerTargetMixin):
    """
    전략 B(점진적 리밸런싱) 전환 기간 관리.
    전환 도중 Trigger A/B/C가 발생하면 STAGE 4와 같은 규칙으로 목표 비중을 수정합니다.
      - A·C·B-1: 희석 매수 중단, 매도 대금은 부족 현금에 우선 사용 후 현금 대기
      - B-2    : 하향된 등급으로 목표 재설정, 채권·현금성 자산만 매수
    """

    def __init__(self, profile: FinancialProfile, survey: SurveyAnswers, portfolio: Portfolio,
                 instruments: dict, data_link=DataLink.MYDATA, realized_overseas_gain_ytd: float = 0.0):
        self._init_risk_state(profile, survey)
        self.portfolio = portfolio
        self.instruments = instruments
        self.data_link = _as_data_link(data_link)
        self.state = soft_migration_analysis(portfolio, self.targets)
        self.state.realized_overseas_net = realized_overseas_gain_ytd
        self.days_elapsed = 0
        self.completed = False
        self._last_plan: Optional[SoftPlan] = None
        self._last_trig: set = set()

    def analysis_report(self) -> list:
        st = self.state
        out = []
        for t in st.locked:
            out.append(f"고정 자산: {self.portfolio.find(t).name}")
        for t, why in st.deferred.items():
            out.append(f"유예 자산: {self.portfolio.find(t).name} ({why})")
        out.append(f"해외주식 비과세 여유: {won(st.tax_room)}")
        return out

    def step(self, snap: LedgerSnapshot, one_off_event: bool = True, days_passed: int = 30) -> tuple:
        snap = self._resolve_snapshot(snap)
        log, orders = [], []
        self.days_elapsed += days_passed
        self.buffer_history.append(snap.buffer)
        reserve = self.c_reserve(snap.essential_expense)
        trig, hold_notes = self._scan_triggers(snap, reserve, monthly=True)
        log += self._header(snap, reserve, trig) + hold_notes
        self._log_temporary_targets(trig, log)
        self._handle_a_recovery(snap, trig, one_off_event, log)
        self._handle_b(snap, trig, log)
        self.state.targets = self.targets          # 트리거로 바뀐 목표를 전환 계획에 반영

        need = 0.0
        if Trigger.C in trig:
            need = max(0.0, snap.upcoming_cf - snap.c_current)
            log.append(f"[Trigger C] 부족액 {won(need)} → 매도 대금 우선 충당, 희석 매수 유예")
        elif Trigger.A in trig:
            need = max(0.0, reserve - snap.c_current)
            log.append(f"[Trigger A] 부족액 {won(need)} → 매도 대금 우선 충당, 희석 매수 동결")

        if self._b1_hold_only(trig):
            log.append("[B-1] 전환 매매 일시 중지: 등급 변동 비중 조정 외 보유 자산 매도 없음")
            b1_orders, _ = self._b1_adjust_orders(trig, log)
            orders += b1_orders
            orders += self._b1_cash_orders(snap, trig, log)
            self._last_plan, self._last_trig = None, trig
            self.prev_triggers = trig
            return log, OrderProposal(orders, "전략 B 매매 제안 (B-1)")

        kw = dict(hold_buys=self._is_frozen(snap, trig), safe_only=self._b2_safe_only(snap, trig),
                  cash_need=need, equity_rotation=self.b2_equity_rotation,
                  sell_deadline_days=snap.deadline() if Trigger.C in trig else None)
        if not self.state.initial_done:
            log.append("[Step 2] 1차 매매")
            plan = soft_migration_initial_plan(self.portfolio, self.state, self.instruments, **kw)
        else:
            log.append("[Step 3] 희석 매수 · 단계적 매도")
            plan = soft_migration_dilution_step(self.portfolio, self.state, snap.free_cash,
                                                self.instruments, **kw)
        orders += plan.orders
        log += plan.notes

        a_extra = []
        if plan.uncovered_need > 0:
            after_sells = self.portfolio.apply(plan.sell_orders, self.instruments)
            adj = copy.copy(snap)
            adj.c_current = snap.c_current + plan.withdrawn
            if Trigger.C in trig:
                extra = handle_trigger_c(adj, after_sells, self.targets, self._overseas_ytd())
                orders += extra.orders
                log.append(f"  남은 {won(plan.uncovered_need)} → 매도 점수(Score_i) 순 추가 현금화")
            else:
                extra = handle_trigger_a(adj, reserve, after_sells, self.targets)
                orders += extra.orders
                a_extra = extra.orders
                log.append(f"  남은 {won(plan.uncovered_need)} → {extra.mode}: {extra.note}")
        if Trigger.A in trig and Trigger.C not in trig:
            self._plan_emergency_transfer(self._a_transfer_amount(snap, a_extra, plan.withdrawn), log)

        orders += self._b1_cash_orders(snap, trig, log)
        after = self.portfolio.apply(orders, self.instruments)
        log += dilution_outlook(after, self.state, snap.free_cash)

        sells = [o for o in orders if o.side == "매도"]
        buys = [o for o in orders if o.side == "매수"]
        cost = summarize_sell_costs(self.portfolio, sells, buys, self.state.realized_overseas_net)
        self._last_plan, self._last_trig = plan, trig
        self.prev_triggers = trig
        return log, OrderProposal(orders, "전략 B 매매 제안", extra=cost.lines())

    def confirm(self, proposal: OrderProposal) -> str:
        """승인·체결 반영 → Step 4 완료 판정 + 전환 3중 검증"""
        before = self.portfolio
        self.portfolio = self.portfolio.apply(self._executable(proposal), self.instruments)
        self._commit_emergency_transfer()
        for o in self._executable(proposal):          # 해외 실현 손익(상계용) 누적
            h = before.find(o.ticker)
            if o.side == "매도" and h:
                self.state.realized_overseas_net += _overseas_gain(h, o.amount)
        if self._last_plan and self._last_plan.is_initial:
            self.state.initial_done = True
        for t in list(self.state.deferred):
            if not self.portfolio.find(t):
                self.state.deferred.pop(t)

        adj = locked_adjusted_targets(self.portfolio, self.targets)
        if self.days_elapsed >= TRANSITION_TIMEOUT_DAYS:
            ok, msg = transition_ready(self.portfolio, adj, "B", self._last_trig,
                                       self.data_link, self.days_elapsed)
        elif not soft_migration_completed(self.portfolio, self.state):
            left = [self.portfolio.find(t).name for t in self.state.deferred if self.portfolio.find(t)]
            ok, msg = False, ("유예 자산 정리 대기: " + ", ".join(left)) if left else "비중 오차 ±3.0%p 미달"
        else:
            ok, msg = transition_ready(self.portfolio, adj, "B", self._last_trig,
                                       self.data_link, self.days_elapsed)
        self.completed = ok
        return msg


# ════════════════════════════════════════════════════════════════════
# 통합 오케스트레이터 (정식 관리 모드)
# ════════════════════════════════════════════════════════════════════
class PortfolioManager(TriggerTargetMixin):
    def __init__(self, profile: FinancialProfile, survey: SurveyAnswers,
                 portfolio: Portfolio, instruments: dict, data_link=DataLink.MYDATA):
        self._init_risk_state(profile, survey)
        self.data_link = _as_data_link(data_link)
        self.portfolio = portfolio
        self.instruments = instruments
        self.days_since_rebalance = 0
        self.realized_overseas_net = 0.0   # 올해 해외주식 실현 손익(상계용)
        self.expense_reserve = 0.0         # Trigger C로 확보한 지출 대기 현금
        self.seasonal = SeasonalPlanner()   # 1년치 지출 패턴 → 비정기 지출 직전 달 현금 선적립
        self.seasonal_reserves: dict = {}   # 대상 달(YYYY-MM) → 계절성 지출 대비 적립 현금 (투자 비중 계산 제외)
        self.tax_reserve = 0.0              # 비정기 사업·용역 소득의 세금 대비 적립금
        self.irregular_dca_queue: list = [] # 목돈 비정기 수입의 다음 달 이후 분할 매수 예정액
        self._planned_expense_reserve = 0.0

    def monthly_cycle(self, snap: LedgerSnapshot, one_off_event: bool = True,
                      today: Optional[date] = None) -> tuple:
        """
        월 마감 루프: 월중 수시 스캔에서 발생했던 트리거까지 포함해 회복·복귀를 판단
        today: 실제 마감(판단)일. 주면 그 날짜로 트리거 유지 일수·재진입·정산일을 계산하고,
               없으면 가계부 월의 다음 달 1일로 간주 (시뮬레이션·데모 호환)
        """
        self.prev_triggers = set(self.prev_triggers) | getattr(self, "event_triggers", set())
        self._event_handled = {}
        self.event_triggers = set()
        self._close_today = today
        try:
            return self._monthly_cycle(snap, one_off_event)
        finally:
            self._close_today = None

    def plan_irregular(self, snap: LedgerSnapshot, seasonal_from_free: float = 0.0) -> IrregularPlan:
        """비정기 수입 배분 계획 (상태 변경 없음)"""
        if snap.irregular_income <= 0:
            return IrregularPlan(0.0)
        reserve_need = self.c_reserve(snap.essential_expense)
        balance = snap.emergency_balance if snap.emergency_balance is not None else (self.last_emergency_balance or 0)
        emergency_short = max(0.0, reserve_need - balance)
        upcoming, seasonal_short = 0.0, 0.0
        if snap.period:
            y, m = int(snap.period[:4]), int(snap.period[5:7])
            ny, nm = (y + 1, 1) if m == 12 else (y, m + 1)
            start = date(ny, nm, 1)
            cal = getattr(self.seasonal, "calendar", None)
            if cal is not None:
                big = sum(e.amount for e in cal.user_events
                          if e.big and 0 <= (e.day - start).days <= IRREGULAR_UPCOMING_DAYS)
                spare = max(0.0, balance - reserve_need)              # 비상금 초과분은 먼저 쓸 수 있는 돈
                upcoming = max(0.0, big - getattr(self, "expense_reserve", 0.0) - spare)
            extra, _ = self.seasonal.expected_extra(ny, nm)
            have = self.seasonal_reserves.get(f"{ny}-{nm:02d}", 0.0) + seasonal_from_free
            seasonal_short = max(0.0, extra - have)
        return plan_irregular_income(snap.irregular_income, snap.irregular_taxable,
                                     emergency_shortage=emergency_short, upcoming_shortfall=upcoming,
                                     seasonal_shortfall=seasonal_short, portfolio_total=self.portfolio.total())

    def _commit_irregular(self, snap: LedgerSnapshot, plan: IrregularPlan, log: list) -> float:
        """배분 확정: 비상금 이체·지출 대기·계절 대비·세금 몫 적립, 이번 달 투자액 반환"""
        if plan.amount <= 0:
            return 0.0
        log += plan.lines()
        if plan.to_emergency:
            self._plan_emergency_transfer(plan.to_emergency, log)
        if plan.to_upcoming:
            self.expense_reserve += plan.to_upcoming
        if plan.to_seasonal and snap.period:
            y, m = int(snap.period[:4]), int(snap.period[5:7])
            t = f"{y + (m == 12)}-{m % 12 + 1:02d}"
            self.seasonal_reserves[t] = self.seasonal_reserves.get(t, 0.0) + plan.to_seasonal
        if plan.to_tax:
            self.tax_reserve += plan.to_tax
            log.append(f"  세금 대비 적립금 누적 {won(self.tax_reserve)} (파킹통장 보관, 투자 비중 계산 제외)")
        self.irregular_dca_queue += plan.invest_later
        return plan.invest_now

    def _pop_irregular_installment(self, log: list) -> float:
        if not self.irregular_dca_queue:
            return 0.0
        amt = self.irregular_dca_queue.pop(0)
        log.append(f"비정기 수입 분할 매수분 {won(amt)} 추가 (남은 회차 {len(self.irregular_dca_queue)})")
        return amt

    def _apply_expense_reserve(self, snap: LedgerSnapshot, log: list) -> None:
        """지출 대기 현금을 스냅샷에 반영, 예정 지출이 없어지면(지출 완료·취소) 정리"""
        if self.expense_reserve > 0 and snap.upcoming_cf <= 0:
            log.append(f"[Trigger C 해제] 예정 지출 종료 → 지출 대기 현금 {won(self.expense_reserve)} 정리")
            self.expense_reserve = 0.0
        snap.expense_reserved = self.expense_reserve
        if self.expense_reserve > 0:
            log.append(f"지출 대기 현금 {won(self.expense_reserve)} 확보 중 (Trigger C 판단에 포함)")

    def _monthly_cycle(self, snap: LedgerSnapshot, one_off_event: bool = True) -> tuple:
        """월간 루프 1회 실행 → (보고서 줄 목록, 매매 제안)"""
        snap = self._resolve_snapshot(snap)
        log, orders = [], []
        self._apply_expense_reserve(snap, log)
        if snap.period:
            used = self.seasonal_reserves.pop(snap.period, 0.0)
            if used > 0:
                log.append(f"[계절성 대비] {snap.period} 비정기 지출에 대비금 {won(used)} 사용 처리")
            self.seasonal.add(snap.period, snap.monthly_expenses)
        self.buffer_history.append(snap.buffer)
        self.days_since_rebalance += 30
        reserve = self.c_reserve(snap.essential_expense)
        trig, hold_notes = self._scan_triggers(snap, reserve, monthly=True)
        log += self._header(snap, reserve, trig) + hold_notes
        self._log_temporary_targets(trig, log)

        if Trigger.C in trig:
            plan = handle_trigger_c(snap, self.portfolio, self.targets, self._overseas_ytd())
            if plan.shortage <= 0.5:
                log.append("[Trigger C] 해제 대기 — 추가 매도 없이 신규 매수 전면 유예 유지")
            else:
                log.append(f"[Trigger C] 부족액 {won(plan.shortage)} → 신규 매수 전면 유예")
                log += plan.score_table()
            orders += plan.orders
            self._planned_expense_reserve += sum(o.amount for o in plan.orders)
            self._event_handled["C"] = plan.shortage
            if plan.uncovered > 0:
                log.append(f"  ⚠ D-Day 내 정산 가능한 자산으로 {won(plan.uncovered)} 부족")

        if Trigger.A in trig and Trigger.C not in trig and snap.c_current >= reserve:
            log.append("[Trigger A] 해제 대기 — 추가 매도 없이 신규 매수 동결, 잉여금은 계속 비상금 계좌로")
            self._plan_emergency_transfer(self._a_transfer_amount(snap, [], snap.irregular_income), log)
        elif Trigger.A in trig and Trigger.C not in trig:
            plan = handle_trigger_a(snap, reserve, self.portfolio, self.targets)
            log.append(f"[Trigger A] 부족액 {won(plan.shortage)} → {plan.mode}: {plan.note}")
            orders += plan.orders
            self._plan_emergency_transfer(self._a_transfer_amount(snap, plan.orders, snap.irregular_income), log)
            if snap.irregular_income:
                log.append(f"비정기 수입 {won(snap.irregular_income)}도 비상금 복구에 먼저 사용")
            self._event_handled["A"] = plan.shortage

        self._handle_a_recovery(snap, trig, one_off_event, log)
        self._handle_b(snap, trig, log)

        if self._is_frozen(snap, trig):
            log.append("위험 자산 신규 매수 동결 (Hard Freeze)")
            if snap.irregular_income and Trigger.A not in trig:
                log.append(f"비정기 수입 {won(snap.irregular_income)}은 매수 동결 중이라 현금으로 보관")
            b1_orders, net = self._b1_adjust_orders(trig, log)
            orders += b1_orders
            self.realized_overseas_net += net
            orders += self._b1_cash_orders(snap, trig, log)
        else:
            if self._b2_safe_only(snap, trig):
                # B-2: 수익권 초과 위험 자산 단계적 매도 + 잉여 현금 → 채권·현금성 자산 (밴드 매매 대신)
                sells, n1, net = b2_gradual_exit(
                    self.portfolio, self.targets,
                    tax_room=max(0.0, OVERSEAS_TAX_FREE_LIMIT - self.realized_overseas_net))
                self.realized_overseas_net += net
                adj_t = locked_adjusted_targets(self.portfolio, self.targets)
                gaps = self.portfolio.gaps(adj_t)
                under = {c: -g for c, g in gaps.items() if g < 0}
                settle = max((self.portfolio.find(o.ticker).settlement_days for o in sells), default=0)
                total = self.portfolio.total()
                deficits = {c: total * g / 100 for c, g in under.items()}
                buys, n2, _, _ = _route_proceeds(
                    sum(o.amount for o in sells) + max(0.0, snap.free_cash)
                    + self._pop_irregular_installment(log)          # 지난달까지 예약된 분할분 먼저
                    + self._commit_irregular(snap, self.plan_irregular(snap), log), under, self.instruments,
                    settle, hold_buys=False, safe_only=True, cash_need=0.0, reason="B-2 안전자산 교체",
                    **self._equity_rotation_args(sells, deficits))
                orders += sells + buys
                log += n1 + n2
            else:
                log.append(f"이번 달 순잉여금 Free_Cash = 월 확정 수입 {won(snap.monthly_income)} − "
                           f"월 지출 {won(snap.monthly_expenses)} = {won(snap.free_cash)}")
                invest, reserve, snote = self.seasonal.plan(snap.period or "", snap.free_cash)
                if reserve > 0:
                    y, m = int(snap.period[:4]), int(snap.period[5:7])
                    target = f"{y + (m == 12)}-{m % 12 + 1:02d}"
                    self.seasonal_reserves[target] = self.seasonal_reserves.get(target, 0.0) + reserve
                    log.append(f"[계절성 대비] {snote}")
                    log.append(f"  {target} 대비금 {won(self.seasonal_reserves[target])} "
                               f"(파킹통장·CMA 보관, 투자 비중 계산 제외)")
                inst = self._pop_irregular_installment(log)          # 지난달까지 예약된 분할분 먼저
                irr = self._commit_irregular(snap, self.plan_irregular(snap, reserve), log)
                if irr or inst:
                    log.append(f"스마트 바이 재원 = 순잉여금 몫 {won(invest)} + 비정기 수입 {won(irr + inst)}")
                    invest += irr + inst
                log += smart_buy_table(invest, self.portfolio.gaps(self.targets), self.portfolio, self.targets)
                o, n = smart_buy(invest, self.portfolio, self.targets, self.instruments)
                if getattr(self, "account_limits", None):
                    o, ln = route_buys_by_limits(o, self.account_limits)
                    log += ["[계좌 한도] " + x for x in ln]
                orders += o
                log += n
                after = self.portfolio.apply(o, self.instruments)
                due = self.days_since_rebalance >= REBALANCE_PERIOD_MONTHS * 30
                ro, rn, why = mechanical_rebalance(after, self.targets, self.instruments, due)
                if ro or why == "정기 리밸런싱":
                    self.days_since_rebalance = 0
                if why:
                    log.append(f"[기계적 리밸런싱] {why}")
                orders += ro
                log += rn

        if len(self.buffer_history) % 12 == 0 and self.b2_applied_tier is None and Trigger.B not in trig:
            new = annual_recalibration(self.survey, self.buffer_history, self._today())
            if new:
                before = (self.original_tier, dict(self.targets))
                self.risk = new
                self.original_tier = new.tier
                self._set_tier(new.tier)
                self.buffer_old = new.buffer
                log.append(f"[연 1회 재평가] 12개월 평균 Buffer {new.buffer:.1f}% · Horizon {new.horizon:.1f} → "
                           f"Tier {new.tier} {TIER_NAMES[new.tier]} (이전 Tier {before[0]})")
                goals = getattr(self.survey, "goals", None)
                if goals is not None:
                    log += ["  " + x for x in goals.lines(self._today())]
                    moved = {c: self.targets[c] - before[1].get(c, 0) for c in ASSET_CLASSES
                             if abs(self.targets[c] - before[1].get(c, 0)) >= 0.05}
                    if moved:
                        log.append("  목표 비중 조정: " + ", ".join(f"{c} {before[1].get(c, 0):.1f}→{self.targets[c]:.1f}%"
                                                              for c in moved))

        self.prev_triggers = trig
        return log, OrderProposal(orders, "이번 달 매매 제안")

    def event_scan(self, snap: LedgerSnapshot, source: str, today: Optional[date] = None) -> tuple:
        """
        수시 트리거 스캔 (매일 07:00 정기 업데이트 / 앱 실행 / 대형 출금·결제 알림)
        - Trigger A·B·C 발생 여부를 즉시 판단
        - 발생 시 '목표 비중 조절 모드' 작동: STAGE 4와 같은 규칙으로 목표 비중 수정·매수 동결·
          필요 시 유동성 확보 매도 제안
        - 같은 트리거를 하루에 여러 번 스캔해도, 부족액이 늘어난 경우에만 추가 대응 (중복 주문 방지)
        - 회복·복귀 판단과 스마트 바이·리밸런싱은 월 마감(monthly_cycle)에서
        snap: 월중 실시간 스냅샷 (비상금 계좌 잔액 필수, _resolve_snapshot 을 거치지 않음)
        """
        log, orders = [f"[{source}] Trigger A·B·C 스캔"], []
        self.clock = today or clock_today()
        snap = copy.copy(snap)
        if snap.as_of is None:
            snap.as_of = self.clock
        self._apply_expense_reserve(snap, log)
        reserve = self.c_reserve(snap.essential_expense)
        trig, hold_notes = self._scan_triggers(snap, reserve, monthly=False)
        log += self._header(snap, reserve, trig) + hold_notes
        handled = self.__dict__.setdefault("_event_handled", {})
        if not trig:
            log.append("트리거 없음 → 현재 목표 비중 유지")
            return log, OrderProposal([], f"{source} 스캔 결과")

        log.append("⚙ 목표 비중 조절 모드 작동")
        self._log_temporary_targets(trig, log)
        if Trigger.C in trig:
            shortage = max(0.0, snap.upcoming_cf - snap.c_current - snap.expense_reserved)
            if shortage <= 0.5:
                log.append("[Trigger C] 해제 대기 — 추가 매도 없이 신규 매수 유예 유지")
            elif shortage > handled.get("C", 0.0) + 0.5:
                plan = handle_trigger_c(snap, self.portfolio, self.targets, self._overseas_ytd())
                orders += plan.orders
                handled["C"] = shortage
                self._planned_expense_reserve += sum(o.amount for o in plan.orders)
                log.append(f"[Trigger C] 부족액 {won(shortage)} → 신규 매수 유예, 매도 점수 순 현금화 제안")
                if plan.uncovered > 0:
                    log.append(f"  ⚠ D-Day 내 정산 가능한 자산으로 {won(plan.uncovered)} 부족")
            else:
                log.append("[Trigger C] 이미 대응 중 (부족액 변화 없음)")
        if Trigger.A in trig and Trigger.C not in trig:
            shortage = max(0.0, reserve - snap.c_current)
            if shortage <= 0.5:
                log.append("[Trigger A] 해제 대기 — 추가 매도 없이 신규 매수 동결 유지")
            elif shortage > handled.get("A", 0.0) + 0.5:
                plan = handle_trigger_a(snap, reserve, self.portfolio, self.targets)
                orders += plan.orders
                handled["A"] = shortage
                log.append(f"[Trigger A] 부족액 {won(shortage)} → {plan.mode}: {plan.note}")
                self._plan_emergency_transfer(sum(o.amount for o in plan.orders), log)
            else:
                log.append("[Trigger A] 이미 대응 중 (부족액 변화 없음)")
        if Trigger.B in trig:
            self._handle_b(snap, trig, log, monthly=False)
            if self._b1_hold_only(trig):
                b1_orders, net = self._b1_adjust_orders(trig, log)
                orders += b1_orders
                self.realized_overseas_net += net
        if self._is_frozen(snap, trig):
            log.append("신규 매수 동결 (월 마감 전까지 스마트 바이·리밸런싱 매수 중단)")
        self.event_triggers = getattr(self, "event_triggers", set()) | trig
        return log, OrderProposal(orders, f"{source} 목표 비중 조절 제안")

    def set_account_limits(self, api: AccountLimitAPI) -> list:
        """계좌별 잔여 한도 연동: 신규 자금 매수를 한도 안에서 절세 계좌 우선 배정"""
        self.account_limits = api.fetch_limits()
        self.set_tax_accounts(tuple(self.account_limits) + ("일반",))
        return [l.summary() for l in self.account_limits.values()]

    def set_tax_accounts(self, available: tuple) -> None:
        """보유한 계좌 목록(예: ("ISA", "연금저축", "일반")) → 매수 종목을 절세 계좌 우선으로 배정"""
        self.instruments = assign_buy_accounts(self.instruments, available)

    def refresh_valuation(self, result: "ValuationResult") -> None:
        """실시간 평가 결과로 포트폴리오 갱신 (Current_Ratio_i 재산출)"""
        self.portfolio = result.portfolio

    def daily_rebalance_check(self, today: date) -> tuple:
        """
        기계적 리밸런싱 (매일 07:00 정기 업데이트 후)
        - 목표 비중은 투자 등급에 따라 고정: 시장이 오르내려도 목표를 바꾸지 않고,
          가격 변동으로 벌어진 오차만 되돌림
        - 전일 종가 기준으로 어떤 자산군이든 ±5%p를 넘으면 초과 자산 매도 → 미달 자산 매수 제안
          (정산 시차 T+2, 절세 계좌 우선, 거래대금·최소 주문 단위 가드 적용 / 실제 발주는 장중 발주 직전 점검)
        - 트리거 대응 중(A·B·C), B-1·B-2 적용 중, 가계부 미입력 매수 중단 중에는 실행하지 않음
        """
        log = [f"[기계적 리밸런싱 점검] {today} — 고정 목표 비중 대비 ±{REBALANCE_BAND:.0f}%p 이탈 확인"]
        blockers = []
        if getattr(self, "event_triggers", set()):
            blockers.append("트리거 대응 중")
        if self.b1_active or self.b2_applied_tier is not None:
            blockers.append("B-1·B-2 적용 중 (등급 변동 조정 규칙 우선)")
        if self.ledger_frozen:
            blockers.append("가계부 미입력으로 매수 중단 중")
        if blockers:
            log.append("건너뜀: " + ", ".join(blockers))
            return log, OrderProposal([], "기계적 리밸런싱")
        last = getattr(self, "last_rebalance_date", None)
        if last is None:                              # 관리 시작일부터 6개월 주기 계산
            self.last_rebalance_date = last = today
        next_due = add_months(last, REBALANCE_PERIOD_MONTHS)
        targets = locked_adjusted_targets(self.portfolio, self.targets)
        gaps = self.portfolio.gaps(targets)
        worst = max(gaps.items(), key=lambda kv: abs(kv[1]))
        log.append(f"최대 이탈: {worst[0]} {worst[1]:+.1f}%p / 정기 리밸런싱 예정일 {next_due}")
        orders, notes, why = mechanical_rebalance(self.portfolio, targets, self.instruments, today >= next_due)
        log += notes
        if orders or why == "정기 리밸런싱":
            self.last_rebalance_date = today
        if orders:
            log.append(f"{why} → Gap ≥ 목표 초과 자산 일부 매도로 현금 확보 → 미달 자산 매수 제안 "
                       f"(장중 발주 직전 점검 후 발주)")
        return log, OrderProposal(orders, f"기계적 리밸런싱 제안 ({why})" if why else "기계적 리밸런싱")

    def confirm(self, proposal: OrderProposal) -> None:
        """승인·체결 반영 + 비상금 계좌 시스템 이체 확정 + Trigger C 지출 대기 현금 확정"""
        self.portfolio = self.portfolio.apply(self._executable(proposal), self.instruments)
        self._commit_emergency_transfer()
        self.expense_reserve += self._planned_expense_reserve
        self._planned_expense_reserve = 0.0


# ════════════════════════════════════════════════════════════════════
# 가계부 연동 데이터 레이어
#   - 마이데이터 거래 내역 → 필수 지출 자동 분류 → 사용자 확인·수정 → 월간 가계부
#   - 수입 기준: '이번 달 확정 수입' (이번 달 들어온 정기 수입 실수령액)
#   - 보유 종목: 증권사 API 자동 수집 (마이데이터·직접 입력 사용자 공통)
# ════════════════════════════════════════════════════════════════════
@dataclass
class Transaction:
    """마이데이터 입출금·카드 거래 1건"""
    tx_id: str
    tx_date: date
    description: str        # 가맹점·적요
    amount: float           # 양수
    kind: str               # "입금" / "출금"
    category: str = ""      # 금융사 제공 업종·카테고리 (있으면 참고)
    biz_no: str = ""        # 사업자등록번호 (제공 시 가맹점 식별 1순위)
    card_merchant_id: str = ""   # 카드사 가맹점 번호 (제공 시 2순위)
    counterparty: str = ""  # 상대 계좌 식별값 (본인 계좌 간 이체 판별용)
    account: str = ""       # 거래가 발생한 계좌 식별값 (비상금 계좌 자체 거래 판별용)


# (키워드, 분류명, 필수 여부, 확신도) — 확신도 "자동": 그대로 반영 / "확인 필요": 사용자 확인 목록에 표시
EXPENSE_RULES = [
    (("본인계좌", "내계좌", "증권", "CMA", "적금이체"), "본인 계좌 이체(지출 아님)", None, "자동"),
    (("카드대금", "카드결제대금"), "카드대금 출금(카드 승인과 중복, 지출 아님)", None, "자동"),
    (("월세", "관리비", "임대료"), "주거비", True, "자동"),
    (("대출", "원리금", "이자상환", "학자금"), "대출 원리금", True, "자동"),
    (("전기", "가스", "수도", "도시가스", "통신", "SKT", "KT", "LG U+", "인터넷"), "공과금·통신", True, "자동"),
    (("보험",), "보험료", True, "자동"),
    (("병원", "약국", "의원", "치과"), "의료", True, "자동"),
    (("교통카드", "지하철", "버스", "대중교통"), "대중교통", True, "자동"),
    (("마트", "이마트", "홈플러스", "롯데마트", "식자재", "정육", "농협하나로"), "식비(장보기)", True, "자동"),
    (("어린이집", "유치원", "학교"), "보육·교육", True, "자동"),
    (("영화", "CGV", "여행", "항공", "호텔", "게임", "백화점", "주점", "노래방"), "여가·쇼핑", False, "자동"),
    (("넷플릭스", "유튜브", "디즈니", "멜론", "구독"), "구독 서비스", False, "자동"),
    (("쿠팡", "네이버페이", "11번가", "G마켓", "온라인"), "온라인 쇼핑(생필품 여부 확인)", False, "확인 필요"),
    (("배달의민족", "배민", "요기요", "쿠팡이츠"), "배달 음식", False, "확인 필요"),
    (("카페", "스타벅스", "커피"), "카페", False, "확인 필요"),
    (("편의점", "GS25", "CU", "세븐일레븐"), "편의점", False, "확인 필요"),
    (("택시", "주유", "주차"), "자가·택시 교통", False, "확인 필요"),
    (("학원",), "학원비", True, "확인 필요"),
]
INCOME_RULES = [
    (("본인계좌", "내계좌", "증권", "CMA"), "본인 계좌 이체(수입 아님)", None, "자동"),
    (("급여", "월급", "봉급", "임금"), "급여(정기)", True, "자동"),
    (("연금",), "연금(정기)", True, "자동"),
    (("이자", "배당", "환급", "캐시백"), "이자·배당·환급(비정기)", False, "자동"),
    (("상여", "성과급", "보너스"), "상여(비정기)", False, "확인 필요"),
    (("사업", "용역", "프리랜서", "정산"), "사업·용역 소득", True, "확인 필요"),
]


def _norm(text: str) -> str:
    return "".join(ch for ch in text.upper() if not ch.isdigit() and not ch.isspace())


# ── 가맹점 식별: ① 사업자등록번호 → ② 카드사 가맹점 번호 → ③ 대표 가맹점명 사전 → ④ 이름 정규화
CORP_MARKERS = ("(주)", "㈜", "주식회사", "(유)", "유한회사")
PG_PREFIXES = ("KCP*", "NICE*", "KG이니시스", "이니시스", "토스페이먼츠", "PAYCO*", "카카오페이*", "네이버페이*")
MEMO_WORDS = ("자동이체", "정기결제", "결제", "승인", "출금", "입금")
MERCHANT_ALIASES = {
    "쿠팡": ("쿠팡", "COUPANG", "로켓배송"),
    "이마트": ("이마트", "EMART"),
    "홈플러스": ("홈플러스", "HOMEPLUS"),
    "배달의민족": ("배달의민족", "배민", "우아한형제들"),
    "스타벅스": ("스타벅스", "STARBUCKS"),
    "GS25": ("GS25",),
    "CU": ("CU",),
    "세븐일레븐": ("세븐일레븐", "7ELEVEN"),
    "네이버쇼핑": ("네이버쇼핑", "스마트스토어"),
}
KNOWN_MIXED = {"쿠팡", "네이버쇼핑", "GS25", "CU", "세븐일레븐"}   # 필수·비필수가 섞이는 대표 가맹점


def normalize_merchant(desc: str) -> str:
    """법인 표기·결제대행 접두어·지점명·숫자/날짜·적요 단어 제거"""
    t = desc
    for m in CORP_MARKERS + PG_PREFIXES:
        t = t.replace(m, " ")
    t = re.sub(r"\d+[/.\-]\d+", " ", t)
    t = re.sub(r"[#*()\[\]_/.,\-]", " ", t)
    t = re.sub(r"\d+", " ", t)
    tokens = [w for w in t.split() if w not in MEMO_WORDS]
    kept = [w for i, w in enumerate(tokens)
            if i == 0 or not re.fullmatch(r".*(지점|호점|점)", w)]
    return "".join(kept).upper()


def match_alias(norm_name: str) -> Optional[str]:
    for canon, aliases in MERCHANT_ALIASES.items():
        for a in aliases:
            a_n = a.upper()
            if (len(a_n) <= 3 and norm_name == a_n) or (len(a_n) > 3 and a_n in norm_name) \
                    or (len(a_n) <= 3 and norm_name.startswith(a_n) and len(norm_name) <= len(a_n) + 4):
                return canon
    return None


@dataclass
class MerchantId:
    keys: list          # [("BIZ", ...), ("CARD", ...), ("ALIAS"|"NAME", ...)]
    name: str           # 표시용 대표 가맹점명


def identify_merchant(tx: Transaction) -> MerchantId:
    keys = []
    if tx.biz_no:
        keys.append(("BIZ", tx.biz_no))
    if tx.card_merchant_id:
        keys.append(("CARD", tx.card_merchant_id))
    norm = normalize_merchant(tx.description)
    alias = match_alias(norm)
    if alias:
        keys.append(("ALIAS", alias))
        return MerchantId(keys, alias)
    keys.append(("NAME", norm))
    return MerchantId(keys, norm or tx.description)


# 사용자 수정 적용 범위
SCOPE_ONCE = "이번 건만"
SCOPE_MERCHANT = "가맹점 전체"
SCOPE_AMOUNT = "가맹점 금액대"
SCOPE_CATEGORY = "가맹점 업종"


@dataclass
class MerchantRule:
    """가맹점 단위 사용자 규칙"""
    name: str
    kind: str                                              # "입금" / "출금"
    wide: Optional[tuple] = None                           # (include, label) 가맹점 전체
    amount_rules: list = field(default_factory=list)       # [(max_amount, include, label)] 금액 이하
    category_rules: dict = field(default_factory=dict)     # 업종 → (include, label)
    history: list = field(default_factory=list)            # [(period, include)] 사용자 수정 이력
    mixed: bool = False                                    # 혼합 성격 가맹점
    last_used: Optional[str] = None


@dataclass
class LedgerItem:
    tx: Transaction
    label: str                   # 분류명
    include: Optional[bool]      # 지출: 필수 여부 / 입금: 확정 수입 여부 / None: 집계 제외(본인 이체 등)
    confidence: str              # "자동" / "확인 필요" / "사용자 수정" / "사용자 규칙…"
    merchant: str = ""
    emergency: int = 0           # +1: 비상금 계좌로 입금 / −1: 비상금 계좌에서 출금

    def __str__(self) -> str:
        if self.emergency:
            mark = "비상금 입금" if self.emergency > 0 else "비상금 출금"
        elif self.include is None:
            mark = "제외"
        elif self.tx.kind == "출금":
            mark = "필수" if self.include else "비필수"
        else:
            mark = "확정 수입" if self.include else "비정기"
        return (f"{self.tx.tx_id} {self.tx.tx_date:%m-%d} {self.tx.description:<18} "
                f"{self.tx.kind} {won(self.tx.amount):>12}  → {mark} ({self.label}, {self.confidence})"
                + (f" [가맹점: {self.merchant}]" if self.merchant else ""))


class LedgerClassifier:
    """
    거래 내역 자동 분류기
    우선순위: 이번 건 사용자 수정 > 가맹점 + 업종/금액 규칙 > 가맹점 전체 규칙(단일 성격일 때)
              > 시스템 기본 규칙(키워드) > 미분류(확인 필요)
    혼합 성격 가맹점(쿠팡·편의점 등, 또는 최근 3개월 사용자 수정이 엇갈린 가맹점)은
    가맹점 전체 규칙만으로 확정하지 않고 '확인 필요' + 제안값으로 표시
    """

    def __init__(self, emergency_accounts: Optional[set] = None, own_accounts: Optional[set] = None):
        self.rules: dict = {}                               # (kind, key) → MerchantRule (여러 키가 같은 규칙 공유)
        self.emergency_accounts = set(emergency_accounts or ())
        self.own_accounts = set(own_accounts or ())         # 본인 계좌(연동 제외 계좌 포함)

    def _find_rule(self, tx: Transaction, mid: MerchantId) -> Optional[MerchantRule]:
        for k in mid.keys:
            r = self.rules.get((tx.kind, k))
            if r:
                return r
        return None

    def _is_emergency(self, tx: Transaction) -> bool:
        return (tx.counterparty and tx.counterparty in self.emergency_accounts) or "비상금" in tx.description

    def classify(self, tx: Transaction, period: str) -> LedgerItem:
        if tx.account and tx.account in self.emergency_accounts:
            # 비상금 계좌 안에서 일어난 거래(이자 입금, 내부 입출금 등) → 잔액으로 반영, 가계부 집계 제외
            return LedgerItem(tx, "비상금 계좌 자체 거래(잔액으로 반영)", None, "자동")
        if self._is_emergency(tx):
            sign = 1 if tx.kind == "출금" else -1
            return LedgerItem(tx, "비상금 계좌 이체(지출·수입 아님)", None, "자동", "", sign)
        if tx.counterparty and tx.counterparty in self.own_accounts:
            return LedgerItem(tx, "본인 계좌 간 이체(지출·수입 아님)", None, "자동")
        mid = identify_merchant(tx)
        r = self._find_rule(tx, mid)
        if r:
            r.last_used = period
            if tx.category and tx.category in r.category_rules:
                inc, lab = r.category_rules[tx.category]
                return LedgerItem(tx, lab, inc, "사용자 규칙(업종)", r.name)
            for max_amt, inc, lab in r.amount_rules:
                if tx.amount <= max_amt:
                    return LedgerItem(tx, lab, inc, f"사용자 규칙({won(max_amt)} 이하)", r.name)
            if r.wide is not None:
                inc, lab = r.wide
                if r.mixed:
                    return LedgerItem(tx, f"{lab} — 혼합 가맹점, 제안값", inc, "확인 필요", r.name)
                return LedgerItem(tx, lab, inc, "사용자 규칙", r.name)
        rules = EXPENSE_RULES if tx.kind == "출금" else INCOME_RULES
        text = _norm(tx.description + tx.category)
        for keywords, label, include, conf in rules:
            if any(_norm(k) in text for k in keywords):
                return LedgerItem(tx, label, include, conf, mid.name)
        return LedgerItem(tx, "미분류 " + ("지출" if tx.kind == "출금" else "입금"), False, "확인 필요", mid.name)

    def learn(self, tx: Transaction, period: str, include: Optional[bool], label: str,
              scope: str, amount_max: Optional[float] = None) -> Optional[MerchantRule]:
        mid = identify_merchant(tx)
        r = self._find_rule(tx, mid)
        if r is None:
            r = MerchantRule(mid.name, tx.kind, mixed=mid.name in KNOWN_MIXED)
        for k in mid.keys:                                  # 사업자번호·카드번호·이름 모두에 연결
            self.rules[(tx.kind, k)] = r
        r.history.append((period, include))
        if scope == SCOPE_MERCHANT:
            r.wide = (include, label)
        elif scope == SCOPE_AMOUNT:
            r.amount_rules.append((amount_max if amount_max is not None else tx.amount, include, label))
            r.amount_rules.sort(key=lambda x: x[0])
        elif scope == SCOPE_CATEGORY and tx.category:
            r.category_rules[tx.category] = (include, label)
        # 최근 3개월 사용자 수정이 필수·비필수로 엇갈리면 혼합 성격으로 전환
        cur = _period_index(period)
        recent = {inc for p, inc in r.history if cur - _period_index(p) <= 2}
        if True in recent and False in recent:
            r.mixed = True
        r.last_used = period
        return r

    def rules_to_review(self, period: str, stale_months: int = 6) -> list:
        """연 1회 점검용: 6개월 이상 안 쓰인 규칙, 사용자 수정이 엇갈린(혼합) 규칙"""
        seen, out = set(), []
        cur = _period_index(period)
        for r in self.rules.values():
            if id(r) in seen:
                continue
            seen.add(id(r))
            if r.last_used and cur - _period_index(r.last_used) >= stale_months:
                out.append(f"{r.name}: {r.last_used} 이후 사용 안 됨 → 유지 여부 확인")
            elif r.mixed and r.wide is not None and not (r.amount_rules or r.category_rules):
                out.append(f"{r.name}: 필수·비필수가 섞인 가맹점 → 금액·업종 조건 설정 권장")
        return out


BALANCE_SOURCE_MYDATA = "마이데이터 연동 잔액"
BALANCE_SOURCE_MANUAL = "직접 입력"


class MonthlyLedgerReview:
    """
    월간 거래 내역 자동 분류 → 사용자 확인·수정 → 월간 가계부(LedgerSnapshot) 생성
    - 필수 고정 지출 = '필수'로 분류된 출금 합계
    - 월 확정 수입   = '확정 수입'으로 분류된 이번 달 입금 합계 (정기 수입 실수령액)
    - 비상금 계좌 입출금액 = 비상금 계좌로 보낸/받은 이체 합계 (자동 반영)
    """

    def __init__(self, period: str, transactions: list, classifier: LedgerClassifier,
                 account_balances: Optional[dict] = None):
        """account_balances: 마이데이터로 조회한 계좌별 잔액 {계좌 식별값: 잔액}"""
        self.period = period
        self.classifier = classifier
        self.account_balances = dict(account_balances or {})
        self.items = {t.tx_id: classifier.classify(t, period) for t in transactions}

    def needs_review(self) -> list:
        return [it for it in self.items.values() if it.confidence == "확인 필요"]

    def set(self, tx_id: str, include: Optional[bool], scope: str = SCOPE_MERCHANT,
            label: str = "", amount_max: Optional[float] = None) -> LedgerItem:
        """
        사용자 수정 (지출: 필수 여부 / 입금: 확정 수입 여부 / None: 집계 제외)
        scope: 이번 건만 · 가맹점 전체 · 가맹점 금액대(amount_max 이하) · 가맹점 업종
        """
        it = self.items[tx_id]
        it.include = include
        it.label = label or it.label.split(" — ")[0]
        it.confidence = "사용자 수정"
        if scope != SCOPE_ONCE:
            r = self.classifier.learn(it.tx, self.period, include, it.label, scope, amount_max)
            it.merchant = r.name
        else:
            self.classifier.learn(it.tx, self.period, include, it.label, SCOPE_ONCE)
        return it

    def confirm_all(self) -> None:
        """남은 '확인 필요' 항목을 자동 분류(제안값) 그대로 확정"""
        for it in self.needs_review():
            it.confidence = "자동(확인 완료)"

    @property
    def essential_expense(self) -> float:
        return sum(it.tx.amount for it in self.items.values()
                   if it.tx.kind == "출금" and it.include and not it.emergency)

    @property
    def confirmed_income(self) -> float:
        return sum(it.tx.amount for it in self.items.values()
                   if it.tx.kind == "입금" and it.include and not it.emergency)

    @property
    def total_expense(self) -> float:
        """월 지출 합계 = 필수 + 비필수 출금 (본인 계좌 이체·비상금 이체·카드대금 중복 제외)"""
        return sum(it.tx.amount for it in self.items.values()
                   if it.tx.kind == "출금" and it.include is not None and not it.emergency)

    @property
    def free_cash(self) -> float:
        return self.confirmed_income - self.total_expense

    @property
    def emergency_deposit(self) -> float:
        return sum(it.tx.amount for it in self.items.values() if it.emergency > 0)

    @property
    def emergency_withdrawal(self) -> float:
        return sum(it.tx.amount for it in self.items.values() if it.emergency < 0)

    @property
    def linked_emergency_balance(self) -> Optional[float]:
        """지정된 비상금 계좌가 모두 마이데이터로 연동돼 있으면 그 잔액 합계, 아니면 None"""
        accts = self.classifier.emergency_accounts
        if accts and all(a in self.account_balances for a in accts):
            return sum(self.account_balances[a] for a in accts)
        return None

    def summary(self) -> list:
        linked = self.linked_emergency_balance
        emg = (f"비상금 계좌 잔액 {won(linked)} ({BALANCE_SOURCE_MYDATA})" if linked is not None else
               f"비상금 계좌 입금 {won(self.emergency_deposit)}·출금 {won(self.emergency_withdrawal)} (자동 반영)")
        out = [f"{self.period} 월 확정 수입 {won(self.confirmed_income)} / 월 지출 합계 {won(self.total_expense)} "
               f"(필수 {won(self.essential_expense)}) / 순잉여금 {won(self.free_cash)} / {emg}"]
        accts = self.classifier.emergency_accounts
        missing = [a for a in accts if a not in self.account_balances]
        if accts and self.account_balances and missing:
            out.append(f"비상금 계좌 일부 미연동({', '.join(missing)}) → 입출금 합산으로 잔액 계산")
        pending = self.needs_review()
        if pending:
            out.append(f"확인 필요 {len(pending)}건 — 자동 분류가 맞는지 확인해 주세요")
        return out

    def to_snapshot(self, emergency_balance: Optional[float] = None, extra_deposit: float = 0.0,
                    extra_withdrawal: float = 0.0, upcoming_cf: float = 0.0,
                    dday: Optional[int] = None) -> LedgerSnapshot:
        """
        비상금 계좌 잔액 결정 순서
          ① 사용자가 직접 입력한 잔액
          ② 비상금 계좌가 마이데이터로 연동돼 있으면 연동 잔액 (입출금·시스템 이체는 참고용, 중복 합산 안 함)
          ③ 그 외: 지난달 잔액 + 비상금 이체 입출금(거래 내역 자동 집계) + 시스템 이체
        extra_*: 거래 내역에 없는 입출금 보정 (③일 때만 의미)
        """
        if self.needs_review():
            raise ValueError("확인 필요 항목이 남아 있습니다. set() 으로 수정하거나 confirm_all() 로 확정해 주세요.")
        source = ""
        balance = emergency_balance
        if balance is not None:
            source = BALANCE_SOURCE_MANUAL
        elif self.linked_emergency_balance is not None:
            balance, source = self.linked_emergency_balance, BALANCE_SOURCE_MYDATA
        return LedgerSnapshot(self.confirmed_income, self.essential_expense, balance,
                              self.emergency_deposit + extra_deposit,
                              self.emergency_withdrawal + extra_withdrawal,
                              upcoming_cf, dday, period=self.period, balance_source=source,
                              total_expense=self.total_expense)


# ── 증권사 API: 보유 종목 자동 수집 (직접 입력 사용자 포함) ──────────
class BrokerDataAPI:
    """증권사 Open API 잔고 조회 인터페이스 (실제 구현은 증권사별로 작성)"""
    def fetch_holdings(self) -> list:
        raise NotImplementedError


class MockBrokerData(BrokerDataAPI):
    """holdings: 보유 종목 목록 또는 현재 잔고를 돌려주는 함수(체결 반영된 실계좌 흉내)"""
    def __init__(self, holdings):
        self._holdings = holdings

    def fetch_holdings(self) -> list:
        src = self._holdings() if callable(self._holdings) else self._holdings
        return copy.deepcopy(src)


USER_HOLDING_FIELDS = ("locked", "maturity_months", "volatility")   # 사용자가 설정·보완한 값은 유지


def sync_holdings(portfolio: Portfolio, api: BrokerDataAPI) -> tuple:
    """
    증권사 잔고로 보유 종목 동기화
    - 수량·현재가·매수 단가는 증권사 값으로 갱신
    - 매도 금지 설정, 채권 잔존만기 등 사용자가 넣은 값은 유지 (API 값이 없을 때)
    반환: (새 포트폴리오, 변경 내역)
    """
    fetched = api.fetch_holdings()
    notes = []
    old = {h.ticker: h for h in portfolio.holdings}
    for h in fetched:
        prev = old.get(h.ticker)
        if prev is None:
            notes.append(f"신규 편입: {h.name} {h.quantity:,.4g}")
            continue
        for f in USER_HOLDING_FIELDS:
            api_val = getattr(h, f)
            if f == "locked":
                setattr(h, f, prev.locked or h.locked)
            elif api_val in (None, 0.0):
                setattr(h, f, getattr(prev, f))
        if abs(prev.quantity - h.quantity) > 1e-9:
            notes.append(f"수량 변경: {h.name} {prev.quantity:,.4g} → {h.quantity:,.4g}")
    for t, h in old.items():
        if t not in {x.ticker for x in fetched}:
            notes.append(f"잔고 없음(매도 완료 등): {h.name}")
    return Portfolio(fetched), notes


# ════════════════════════════════════════════════════════════════════
# 실시간 운영: 매일 07:00 정기 업데이트 + 앱 실행 / 대형 출금·결제 알림 시 트리거 스캔 + 발주 직전 점검
# ════════════════════════════════════════════════════════════════════
DAILY_UPDATE_TIME = dtime(7, 0)  # 정기 업데이트: 은행 일괄 처리·미국 장 마감 이후, 출근 전 확인 가능한 시간
LARGE_TX_MIN = 500_000          # 대형 거래 기준 금액
LARGE_TX_RATIO = 0.2            # 또는 월 필수 지출의 20% 이상 (둘 중 작은 기준 적용)


class MyDataAPI:
    """마이데이터 조회 인터페이스 (실제 구현은 마이데이터 사업자 API로 작성)"""
    def fetch_transactions(self, since: date, until: date) -> list:
        """since 다음 날 ~ until 까지의 입출금·카드 거래"""
        raise NotImplementedError

    def fetch_balances(self, as_of: date) -> dict:
        """계좌별 잔액 {계좌 식별값: 잔액}"""
        raise NotImplementedError


class MockMyData(MyDataAPI):
    def __init__(self, transactions: list, balance_timeline: list):
        self.transactions = transactions
        self.balance_timeline = sorted(balance_timeline, key=lambda x: x[0])   # [(date, {계좌: 잔액})]

    def fetch_transactions(self, since: date, until: date) -> list:
        return [t for t in self.transactions if since < t.tx_date <= until]

    def fetch_balances(self, as_of: date) -> dict:
        cur = {}
        for d, bal in self.balance_timeline:
            if d <= as_of:
                cur = bal
        return dict(cur)


# ── 데이터 제어: 연동 제외 계좌 · 식별 정보 암호화 · 오프라인 현금 · 사용자 수정 ──────
class IdVault:
    """
    계좌번호 등 식별 정보 보호
    - 원본 번호는 저장하지 않고, 비밀키 기반 HMAC-SHA256 토큰(식별용)과 마스킹 문자열(표시용)만 보관
    - 같은 번호는 항상 같은 토큰 → 계좌 매칭 가능, 토큰으로 원본 복원 불가
    - 비밀키는 서버 키 관리 서비스(KMS) 등 코드 밖에 보관
    """

    def __init__(self, secret_key: bytes):
        if not secret_key or len(secret_key) < 16:
            raise ValueError("비밀키는 16바이트 이상이어야 합니다.")
        self._key = secret_key

    def token(self, raw: str) -> str:
        if not raw:
            return ""
        if raw.startswith("acct_"):          # 이미 토큰화된 값
            return raw
        norm = "".join(ch for ch in raw if ch.isalnum())
        return "acct_" + hmac.new(self._key, norm.encode(), hashlib.sha256).hexdigest()[:20]

    @staticmethod
    def mask(raw: str) -> str:
        digits = "".join(ch for ch in raw if ch.isdigit())
        return ("*" * max(0, len(digits) - 4) + digits[-4:]) if digits else "****"


# ── 계좌번호 원본 보관: 이중 암호화 + 비밀번호 확인 후 표시 ─────────────────
try:
    from cryptography.exceptions import InvalidTag
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import padding, rsa
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    try:
        from cryptography.hazmat.primitives.kdf.argon2 import Argon2id
    except ImportError:                                   # 구버전: scrypt 사용
        Argon2id = None
    _CRYPTO_OK = True
except ImportError:
    _CRYPTO_OK = False

REVEAL_MAX_ATTEMPTS = 5          # 비밀번호 연속 실패 허용 횟수
REVEAL_LOCK_MINUTES = 10         # 초과 시 잠금 시간
REVEAL_SECONDS = 30              # 표시 후 자동으로 다시 가리는 시간
MIN_SECRET_LENGTH = 6            # 비밀번호(또는 앱 PIN) 최소 길이


def _derive_kek(secret: str, salt: bytes) -> bytes:
    """비밀번호 → 키 암호화 키(KEK): Argon2id(가능 시) 또는 scrypt"""
    if Argon2id is not None:
        return Argon2id(salt=salt, length=32, iterations=3, lanes=4,
                        memory_cost=64 * 1024).derive(secret.encode())
    return hashlib.scrypt(secret.encode(), salt=salt, n=2 ** 15, r=8, p=1, maxmem=2 ** 26, dklen=32)


@dataclass
class RevealedNumber:
    """일정 시간 동안만 원본을 보여주는 표시 객체"""
    masked: str
    _value: str
    expires_at: datetime
    clock: Callable

    @property
    def value(self) -> str:
        return self._value if self.clock() < self.expires_at else self.masked

    def __str__(self) -> str:
        return self.value


class AccountSecretStore:
    """
    계좌번호 원본 보관 (이중 암호화)
      ① 계좌번호 → 계좌마다 새 데이터 키(AES-256-GCM)로 암호화
      ② 데이터 키 → 공개키(RSA-OAEP)로 잠금  ※ 새 계좌는 비밀번호 없이도 자동 연동 시 추가 가능
      ③ 공개키의 짝인 개인키 → 사용자 비밀번호에서 만든 키(Argon2id/scrypt)로 AES-GCM 잠금
    - 비밀번호·원본 번호는 저장하지 않음 (비밀번호가 틀리면 개인키 복호화가 실패해 자연히 검증됨)
    - 비밀번호 변경 시 개인키만 다시 잠그면 되므로 계좌 데이터는 그대로
    - 안전장치: 연속 5회 실패 시 10분 잠금, 표시 후 30초 뒤 자동 마스킹, 모든 조회·실패 기록
    - 비밀번호를 잊으면 원본 복원 불가 → 마이데이터 재연동으로 복구 (이체는 금융사 발급 토큰으로 처리)
    """

    def __init__(self, secret: str, clock: Callable = datetime.now):
        if not _CRYPTO_OK:
            raise RuntimeError("계좌번호 암호화에는 cryptography 패키지가 필요합니다: pip install cryptography")
        self._check_secret(secret)
        self.clock = clock
        key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
        self._public = key.public_key()
        self._wrap_private(key, secret)
        self.records: dict = {}          # token → (wrapped_dek, nonce, ciphertext, masked)
        self.failures = 0
        self.locked_until: Optional[datetime] = None
        self.access_log: list = []       # (시각, 결과, 대상)

    @staticmethod
    def _check_secret(secret: str) -> None:
        if not secret or len(secret) < MIN_SECRET_LENGTH:
            raise ValueError(f"비밀번호(또는 PIN)는 {MIN_SECRET_LENGTH}자 이상이어야 합니다.")

    def _wrap_private(self, key, secret: str) -> None:
        der = key.private_bytes(serialization.Encoding.DER, serialization.PrivateFormat.PKCS8,
                                serialization.NoEncryption())
        self._salt = os.urandom(16)
        self._pk_nonce = os.urandom(12)
        self._wrapped_private = AESGCM(_derive_kek(secret, self._salt)).encrypt(self._pk_nonce, der, b"pk")

    def _unwrap_private(self, secret: str):
        der = AESGCM(_derive_kek(secret, self._salt)).decrypt(self._pk_nonce, self._wrapped_private, b"pk")
        return serialization.load_der_private_key(der, password=None)

    # ── 저장 (비밀번호 불필요) ────────────────────────────────────
    def store(self, token: str, raw_number: str, masked: str) -> None:
        dek = AESGCM.generate_key(bit_length=256)
        nonce = os.urandom(12)
        ct = AESGCM(dek).encrypt(nonce, raw_number.encode(), token.encode())
        wrapped = self._public.encrypt(dek, padding.OAEP(mgf=padding.MGF1(hashes.SHA256()),
                                                         algorithm=hashes.SHA256(), label=None))
        self.records[token] = (wrapped, nonce, ct, masked)

    # ── 표시 (비밀번호 확인) ─────────────────────────────────────
    def _log(self, result: str, target: str) -> None:
        self.access_log.append((self.clock().strftime("%Y-%m-%d %H:%M:%S"), result, target))

    def reveal(self, token: str, secret: str) -> RevealedNumber:
        now = self.clock()
        masked = self.records[token][3]
        if self.locked_until and now < self.locked_until:
            self._log("잠금 중 요청 거부", masked)
            raise PermissionError(f"비밀번호 {REVEAL_MAX_ATTEMPTS}회 실패로 잠김 — "
                                  f"{self.locked_until:%H:%M} 이후 다시 시도해 주세요.")
        try:
            key = self._unwrap_private(secret)
        except InvalidTag:
            self.failures += 1
            left = REVEAL_MAX_ATTEMPTS - self.failures
            if left <= 0:
                self.locked_until = now + timedelta(minutes=REVEAL_LOCK_MINUTES)
                self.failures = 0
                self._log("비밀번호 실패 → 잠금", masked)
                raise PermissionError(f"비밀번호 {REVEAL_MAX_ATTEMPTS}회 실패 → {REVEAL_LOCK_MINUTES}분간 잠금")
            self._log(f"비밀번호 실패 (남은 {left}회)", masked)
            raise PermissionError(f"비밀번호가 맞지 않습니다. (남은 시도 {left}회)")
        self.failures = 0
        wrapped, nonce, ct, masked = self.records[token]
        dek = key.decrypt(wrapped, padding.OAEP(mgf=padding.MGF1(hashes.SHA256()),
                                                algorithm=hashes.SHA256(), label=None))
        raw = AESGCM(dek).decrypt(nonce, ct, token.encode()).decode()
        self._log("원본 표시", masked)
        return RevealedNumber(masked, raw, now + timedelta(seconds=REVEAL_SECONDS), self.clock)

    def change_secret(self, old: str, new: str) -> None:
        """비밀번호 변경: 개인키만 새 비밀번호로 다시 잠금 (계좌 데이터 재암호화 불필요)"""
        self._check_secret(new)
        if self.locked_until and self.clock() < self.locked_until:
            raise PermissionError(f"잠김 상태입니다 — {self.locked_until:%H:%M} 이후 다시 시도해 주세요.")
        try:
            key = self._unwrap_private(old)
        except InvalidTag:
            self.failures += 1
            self._log("비밀번호 변경 실패", "-")
            if self.failures >= REVEAL_MAX_ATTEMPTS:
                self.locked_until = self.clock() + timedelta(minutes=REVEAL_LOCK_MINUTES)
                self.failures = 0
            raise PermissionError("기존 비밀번호가 맞지 않습니다.")
        self.failures = 0
        self._wrap_private(key, new)
        self._log("비밀번호 변경", "-")


@dataclass
class LinkedAccount:
    token: str
    masked: str
    institution: str
    kind: str                  # 입출금 / CMA / 파킹통장 / 적금 / 청약 / 증권 등
    alias: str = ""
    transfer_token: str = ""   # 이체용 금융사 발급 토큰(예: 오픈뱅킹 이용번호) — 원본 번호 없이 이체
    in_portfolio: bool = False # 투자용 현금성 계좌(포트폴리오 현금성 자산에 포함)
    excluded: bool = False     # 사용자가 연동을 원하지 않는 계좌
    emergency: bool = False    # 비상금 계좌


class DataControl:
    """
    하이브리드 연동의 사용자 제어 레이어
    - 기본은 자동 연동, 사용자가 원하지 않는 계좌는 연동 대상에서 제외
    - 계좌 식별 정보는 IdVault 토큰·마스킹으로만 저장
    - 연동되지 않는 오프라인 현금 등을 현금성 자산으로 수동 추가
    - 자동 연동된 수치(월 수입·필수 지출·비상금 잔액·보유 수량/가격)를 사용자가 직접 수정 (변경 이력 기록)
    """

    OVERRIDE_FIELDS = {"monthly_income": "월 확정 수입", "essential_expense": "필수 고정 지출",
                       "emergency_balance": "비상금 계좌 잔액"}

    def __init__(self, vault: IdVault, secrets: Optional[AccountSecretStore] = None):
        self.vault = vault
        self.secrets = secrets                # 원본 번호 이중 암호화 보관 (없으면 원본 미보관)
        self.accounts: dict = {}              # token → LinkedAccount
        self.offline_cash: dict = {}          # 이름 → (금액, 비상금 포함 여부)
        self.overrides: dict = {}             # (period, field) → (값, 사유)
        self.holding_overrides: dict = {}     # ticker → {"quantity": .., "price": ..}
        self.audit: list = []                 # (시각, 작업, 대상, 이전, 이후, 사유)
        self._last_offline = 0.0

    def _log(self, action: str, target: str, before, after, reason: str = "") -> None:
        self.audit.append((clock_now().strftime("%Y-%m-%d %H:%M"), action, target, before, after, reason))

    # ── 계좌 연동 관리 ───────────────────────────────────────────
    def register_account(self, raw_number: str, institution: str, kind: str, alias: str = "",
                         excluded: bool = False, emergency: bool = False, transfer_token: str = "") -> str:
        tok = self.vault.token(raw_number)
        if excluded and emergency:
            raise ValueError("비상금 계좌는 연동 제외할 수 없습니다. (잔액을 직접 입력하려면 사용자 수정을 이용하세요)")
        self.accounts[tok] = LinkedAccount(tok, self.vault.mask(raw_number), institution, kind,
                                           alias=alias, excluded=excluded, emergency=emergency,
                                           transfer_token=transfer_token,
                                           in_portfolio=(kind in INVESTABLE_CASH_KINDS and not emergency))
        if self.secrets is not None:
            self.secrets.store(tok, raw_number, self.vault.mask(raw_number))
        self._log("계좌 등록", f"{institution} {self.vault.mask(raw_number)}", None,
                  "연동 제외" if excluded else "연동", alias)
        return tok

    def set_excluded(self, raw_or_token: str, excluded: bool, reason: str = "") -> None:
        acc = self.accounts[self.vault.token(raw_or_token)]
        if excluded and acc.emergency:
            raise ValueError("비상금 계좌는 연동 제외할 수 없습니다.")
        self._log("연동 설정 변경", f"{acc.institution} {acc.masked}", acc.excluded, excluded, reason)
        acc.excluded = excluded

    def reveal_account(self, token: str, secret: str) -> RevealedNumber:
        """비밀번호(또는 앱 PIN) 확인 후 계좌번호 원본을 30초간 표시"""
        if self.secrets is None:
            raise RuntimeError("원본 번호를 보관하지 않도록 설정되어 있습니다.")
        acc = self.accounts[token]
        try:
            r = self.secrets.reveal(token, secret)
            self._log("계좌번호 원본 조회", f"{acc.institution} {acc.masked}", None, "성공")
            return r
        except PermissionError as e:
            self._log("계좌번호 원본 조회", f"{acc.institution} {acc.masked}", None, f"실패: {e}")
            raise

    @property
    def excluded_tokens(self) -> set:
        return {t for t, a in self.accounts.items() if a.excluded}

    @property
    def emergency_tokens(self) -> set:
        return {t for t, a in self.accounts.items() if a.emergency}

    @property
    def own_tokens(self) -> set:
        return set(self.accounts)

    def account_list(self) -> list:
        return [f"{a.institution} {a.masked} ({a.kind}{', ' + a.alias if a.alias else ''}) — "
                f"{'연동 제외' if a.excluded else '연동'}{' · 비상금' if a.emergency else ''}"
                for a in self.accounts.values()]

    # ── 마이데이터 결과 정제 (토큰화 + 제외 계좌 제거) ─────────────
    def filter_transactions(self, txs: list) -> list:
        out = []
        for t in txs:
            n = copy.copy(t)
            n.account = self.vault.token(t.account)
            n.counterparty = self.vault.token(t.counterparty)
            if n.account and n.account in self.excluded_tokens:
                continue                          # 연동 제외 계좌의 거래는 수집하지 않음
            out.append(n)
        return out

    def filter_balances(self, balances: dict) -> dict:
        out = {}
        for raw, bal in balances.items():
            tok = self.vault.token(raw)
            if tok not in self.excluded_tokens:
                out[tok] = bal
        return out

    # ── 오프라인 현금 ─────────────────────────────────────────────
    def set_offline_cash(self, name: str, amount: float, in_emergency: bool = True) -> None:
        before = self.offline_cash.get(name, (0.0, in_emergency))[0]
        if amount <= 0:
            self.offline_cash.pop(name, None)
        else:
            self.offline_cash[name] = (amount, in_emergency)
        self._log("오프라인 현금", name, before, amount, "비상금 포함" if in_emergency else "비상금 제외")

    @property
    def offline_emergency_total(self) -> float:
        return sum(a for a, inc in self.offline_cash.values() if inc)

    # ── 사용자 수정 ───────────────────────────────────────────────
    def override(self, period: str, field_name: str, value: Optional[float], reason: str = "",
                 auto_value: Optional[float] = None) -> None:
        """자동 연동 수치 수정 (value=None 이면 수정 취소 → 자동 값으로 복귀)"""
        if field_name not in self.OVERRIDE_FIELDS:
            raise ValueError(f"수정 가능 항목: {', '.join(self.OVERRIDE_FIELDS.values())}")
        label = self.OVERRIDE_FIELDS[field_name]
        if value is None:
            self.overrides.pop((period, field_name), None)
            self._log("사용자 수정 취소", f"{period} {label}", None, "자동 값", reason)
        else:
            self.overrides[(period, field_name)] = (value, reason)
            self._log("사용자 수정", f"{period} {label}", auto_value, value, reason)

    def override_holding(self, ticker: str, quantity: Optional[float] = None,
                         price: Optional[float] = None, reason: str = "") -> None:
        cur = self.holding_overrides.setdefault(ticker, {})
        if quantity is not None:
            cur["quantity"] = quantity
        if price is not None:
            cur["price"] = price
        self._log("보유 종목 수정", ticker, None, dict(cur), reason)

    def clear_holding_override(self, ticker: str) -> None:
        self.holding_overrides.pop(ticker, None)
        self._log("보유 종목 수정 취소", ticker, None, "증권사 값", "")

    # ── 적용 ──────────────────────────────────────────────────────
    def apply_to_snapshot(self, snap: LedgerSnapshot, commit: bool = False) -> LedgerSnapshot:
        """
        오프라인 현금(비상금 포함분)을 잔액에 더하고, 사용자 수정값을 우선 적용
        - 연동 잔액·직접 입력 잔액: 오프라인 현금 전액을 더함
        - 지난달 잔액 기반 자동 계산: 지난 확정 이후 오프라인 현금 증감분만 반영 (이중 합산 방지)
        commit=True(월 마감)일 때만 오프라인 현금 반영 기준을 갱신
        """
        s = copy.copy(snap)
        offline = self.offline_emergency_total
        delta = offline - self._last_offline
        if s.emergency_balance is None:
            s.emergency_deposit += max(0.0, delta)          # 자동 계산 경로: 증감분을 입출금으로 반영
            s.emergency_withdrawal += max(0.0, -delta)
        elif s.balance_source in (BALANCE_SOURCE_MYDATA, BALANCE_SOURCE_MANUAL):
            s.emergency_balance += offline
        else:
            s.emergency_balance += delta
        if commit:
            self._last_offline = offline
        if offline and s.emergency_balance is not None:
            s.balance_source = (s.balance_source or "자동 계산") + f" + 오프라인 현금 {won(offline)}"
        for fname in self.OVERRIDE_FIELDS:
            ov = self.overrides.get((s.period, fname))
            if ov is None:
                continue
            if fname == "emergency_balance":
                s.emergency_balance = ov[0]
                s.balance_source = f"사용자 수정 ({ov[1]})" if ov[1] else "사용자 수정"
            else:
                setattr(s, fname, ov[0])
        return s

    def apply_to_holdings(self, holdings: list) -> list:
        out = []
        for h in holdings:
            ov = self.holding_overrides.get(h.ticker)
            if ov:
                h = copy.copy(h)
                h.quantity = ov.get("quantity", h.quantity)
                h.price = ov.get("price", h.price)
            out.append(h)
        return out


class ControlledMyData(MyDataAPI):
    """마이데이터 응답을 DataControl 로 정제 (식별 정보 토큰화, 연동 제외 계좌 제거)"""

    def __init__(self, api: MyDataAPI, control: DataControl):
        self.api, self.control = api, control

    def fetch_transactions(self, since: date, until: date) -> list:
        return self.control.filter_transactions(self.api.fetch_transactions(since, until))

    def fetch_balances(self, as_of: date) -> dict:
        return self.control.filter_balances(self.api.fetch_balances(as_of))


class ControlledBrokerData(BrokerDataAPI):
    """증권사 잔고에 사용자 수정(수량·가격)을 우선 적용"""

    def __init__(self, api: BrokerDataAPI, control: DataControl):
        self.api, self.control = api, control

    def fetch_holdings(self) -> list:
        return self.control.apply_to_holdings(self.api.fetch_holdings())


INVESTABLE_CASH_KINDS = ("CMA", "MMF", "파킹통장", "예금", "적금")


@dataclass
class ValuationResult:
    at: datetime
    portfolio: Portfolio
    ratios: dict
    sources: list

    def report(self, targets: Optional[dict] = None) -> list:
        lines = [f"실시간 평가 {self.at:%Y-%m-%d %H:%M} — 총 투자 자산 {won(self.portfolio.total())}"]
        cv = self.portfolio.class_values()
        for c in ASSET_CLASSES:
            if cv[c] == 0 and not (targets and targets.get(c)):
                continue
            line = f"  {c:<8} {won(cv[c]):>14}  Current_Ratio {self.ratios[c]:5.1f}%"
            if targets:
                line += f"  Target {targets.get(c, 0):5.1f}%  Gap {self.ratios[c] - targets.get(c, 0):+5.1f}%p"
            lines.append(line)
        return lines


class RealtimeValuation:
    """
    증권·은행 계좌 실시간 평가 → 자산군별 현재 비중 산출
      V_i            = Σ (보유 수량 × 현재가)            … 증권 계좌 (현재가 조회 실패 시 최근 가격)
                     + Σ 투자용 현금성 계좌 잔액          … 은행·증권 CMA/MMF/파킹통장/예적금
      TotalInvestment = Σ_i V_i
      Current_Ratio_i = V_i ÷ TotalInvestment × 100 (%)
    제외: 비상금 계좌(필수 비상금은 투자 자산이 아님), 연동 제외 계좌, 생활비 입출금 계좌
    사용자 수정(보유 수량·가격)은 증권사 값보다 우선
    """

    def __init__(self, holdings_api: BrokerDataAPI, quote_api: BrokerAPI,
                 mydata: Optional[MyDataAPI] = None, control: Optional[DataControl] = None):
        self.holdings_api = holdings_api
        self.quote_api = quote_api
        self.mydata = mydata
        self.control = control

    def scan(self, now: datetime) -> ValuationResult:
        sources = []
        holdings = self.holdings_api.fetch_holdings()
        if self.control:
            holdings = self.control.apply_to_holdings(holdings)
        live = 0
        for h in holdings:
            ov = self.control.holding_overrides.get(h.ticker, {}) if self.control else {}
            q = None if "price" in ov else self.quote_api.get_quote(h.ticker)
            if q:
                h.price = q
                live += 1
        sources.append(f"증권 계좌 {len(holdings)}종목 (실시간 현재가 {live}종목, 나머지 최근 가격)")
        if self.mydata and self.control:
            bal = self.control.filter_balances(self.mydata.fetch_balances(now.date()))
            cash_accts = [a for t, a in self.control.accounts.items()
                          if a.in_portfolio and not a.excluded and not a.emergency and t in bal]
            for a in cash_accts:
                holdings.append(Holding(a.token, f"{a.institution} {a.kind} {a.masked}", CASH,
                                        bal[a.token], 1.0, settlement_days=0))
            sources.append(f"현금성 계좌 {len(cash_accts)}개 (비상금·연동 제외·생활비 계좌 제외)")
        pf = Portfolio(holdings)
        return ValuationResult(now, pf, pf.current_ratios(), sources)


class LiveLedger:
    """
    이번 달 누적 가계부 (월중 실시간)
    - 수입: 이번 달 확정 수입 (아직 급여 전이면 직전 월 확정 수입을 기준값으로 사용)
    - 필수 지출: max(직전 월 필수 지출, 이번 달 누적 필수 지출)
      → 월초 급여 전·지출 일부만 발생한 시점에 잉여율이 왜곡돼 Trigger B가 잘못 발동하는 것을 방지하고,
        월중 지출이 평소보다 커지면 즉시 반영
    - 비상금 계좌 잔액: 마이데이터 연동 잔액 → 없으면 마지막 확정 잔액 + 월중 비상금 입출금
    - 목돈 지출 예정: 사용자가 등록한 이벤트 중 30일 이내 항목
    """

    def __init__(self, period: str, classifier: LedgerClassifier, prev_income: float, prev_essential: float,
                 control: Optional[DataControl] = None):
        self.control = control
        if control is not None:
            classifier.emergency_accounts |= control.emergency_tokens
            classifier.own_accounts |= control.own_tokens
        self.period = period
        self.classifier = classifier
        self.transactions: dict = {}
        self.balances: dict = {}
        self.prev_income = prev_income
        self.prev_essential = prev_essential
        self.events: list = []           # [(이름, 금액, 지출일)]

    def add(self, txs: list) -> list:
        new = [t for t in txs if t.tx_id not in self.transactions]
        for t in new:
            self.transactions[t.tx_id] = t
        return new

    def register_event(self, name: str, amount: float, due: date) -> None:
        self.events.append((name, amount, due))

    def review(self) -> MonthlyLedgerReview:
        return MonthlyLedgerReview(self.period, list(self.transactions.values()), self.classifier, self.balances)

    def upcoming(self, today: date) -> tuple:
        """30일(달력) 이내 목돈 지출: (합계, D-Day, 남은 영업일, 지출일, 대상)"""
        return upcoming_big_expenses(self.events, today)

    def live_snapshot(self, today: date, fallback_balance: float) -> LedgerSnapshot:
        rv = self.review()
        income = rv.confirmed_income if rv.confirmed_income > 0 else self.prev_income
        essential = max(self.prev_essential, rv.essential_expense)
        balance = rv.linked_emergency_balance
        source = BALANCE_SOURCE_MYDATA
        if balance is None:
            balance = fallback_balance + rv.emergency_deposit - rv.emergency_withdrawal
            source = "마지막 확정 잔액 + 월중 비상금 입출금"
        cf, dday, bdays, due, _ = self.upcoming(today)
        snap = LedgerSnapshot(income, essential, balance, rv.emergency_deposit, rv.emergency_withdrawal,
                              cf, dday, period=self.period, balance_source=source, bdays=bdays,
                              due_date=due, as_of=today)
        return self.control.apply_to_snapshot(snap, commit=False) if self.control else snap

    def close_month(self, today: date) -> tuple:
        """월 마감: 확인 필요 항목은 제안값으로 확정 → 월간 가계부 생성, 다음 달 기준값 갱신"""
        rv = self.review()
        pending = len(rv.needs_review())
        rv.confirm_all()
        cf, dday, bdays, due, _ = self.upcoming(today)
        snap = rv.to_snapshot(upcoming_cf=cf, dday=dday)
        snap.bdays, snap.due_date, snap.as_of = bdays, due, today
        if self.control:
            snap = self.control.apply_to_snapshot(snap, commit=True)
        if rv.confirmed_income > 0:
            self.prev_income = rv.confirmed_income
        self.prev_essential = rv.essential_expense
        return snap, pending

    def start_month(self, period: str, today: date) -> None:
        self.period = period
        self.transactions = {}
        self.events = [e for e in self.events if e[2] >= today]


class LiveOperation:
    """
    가계부 연동 관리 모드의 실시간 운영기
    - run_daily_update: 매일 07:00 — 마이데이터 거래·잔고, 증권사 보유 종목·전일 종가를 받아
                        수입·지출·잔고·포트폴리오 비중 업데이트 → 트리거 스캔 → 매매 제안 생성
                        (월이 바뀐 첫 업데이트에는 지난달 마감 → 월간 루프 실행)
                        실제 발주는 장중(10:00~15:00) 발주 직전 점검(pre_trade_check)을 거쳐 진행
    - on_app_open    : 앱 실행 시 — 최신 데이터 조회 후 트리거 스캔
    - on_payment_alert: 대형 출금·결제 알림 수신 시 — 해당 거래 반영 후 트리거 스캔
    트리거 발생 시 PortfolioManager.event_scan 이 '목표 비중 조절 모드'를 작동시킵니다.
    """

    def __init__(self, manager: "PortfolioManager", ledger: LiveLedger,
                 mydata: Optional[MyDataAPI] = None, broker: Optional[BrokerDataAPI] = None,
                 start: Optional[date] = None):
        self.m = manager
        self.ledger = ledger
        self.mydata = mydata
        self.broker = broker
        self.last_sync = start or clock_today()
        self.history: list = []          # (날짜, 출처, 트리거) 기록

    # ── 데이터 갱신 ───────────────────────────────────────────────
    def _refresh(self, today: date) -> list:
        notes = []
        if self.mydata and _as_data_link(self.m.data_link) == DataLink.MYDATA:
            new = self.ledger.add(self.mydata.fetch_transactions(self.last_sync, today))
            self.ledger.balances = self.mydata.fetch_balances(today)
            if new:
                notes.append(f"거래 {len(new)}건 수집")
        if self.broker:
            self.m.portfolio, changes = sync_holdings(self.m.portfolio, self.broker)
            notes += changes
        self.last_sync = max(self.last_sync, today)
        return notes

    def _status(self, today: date) -> list:
        rv = self.ledger.review()
        cur = self.m.portfolio.current_ratios()
        weights = ", ".join(f"{c} {cur[c]:.1f}%" for c in ASSET_CLASSES if cur[c] > 0)
        return [f"{self.ledger.period} 누적: 확정 수입 {won(rv.confirmed_income)} / 필수 지출 "
                f"{won(rv.essential_expense)} / 포트폴리오 {won(self.m.portfolio.total())} ({weights})"]

    def _scan(self, today: date, source: str) -> tuple:
        fallback = (self.m.last_emergency_balance or 0.0) + getattr(self.m, "pending_emergency_transfer", 0.0)
        snap = self.ledger.live_snapshot(today, fallback)
        log, prop = self.m.event_scan(snap, source)
        self.history.append((today, source, sorted(t.name for t in getattr(self.m, "event_triggers", set()))))
        return log, prop

    # ── 이벤트 ────────────────────────────────────────────────────
    def run_daily_update(self, today: date) -> tuple:
        log, proposals = [f"☀ {today} {DAILY_UPDATE_TIME:%H:%M} 정기 업데이트"], []
        period = f"{today.year}-{today.month:02d}"
        closed = period != self.ledger.period
        if closed:
            # 지난달 마지막 날까지 수집 후 월 마감 → 월간 루프(스마트 바이·리밸런싱·회복 판단)
            log += self._refresh(today - timedelta(days=1))
            snap, pending = self.ledger.close_month(today)
            if pending:
                log.append(f"월 마감: 확인 필요 {pending}건은 제안값으로 확정 (앱에서 수정 가능)")
            mlog, mprop = self.m.monthly_cycle(snap)
            log += ["[월 마감] " + x for x in mlog]
            proposals.append(mprop)
            self.ledger.start_month(period, today)
        log += self._refresh(today)
        log += self._status(today)
        if _as_data_link(self.m.data_link) == DataLink.MANUAL:
            for n in self.m.check_ledger_input(today):
                log.append(str(n))
        slog, sprop = self._scan(today, "07:00 정기 업데이트")
        log += slog
        proposals.append(sprop)
        if not sprop.orders and not closed:          # 월 마감일에는 월간 루프에서 이미 리밸런싱 점검
            rlog, rprop = self.m.daily_rebalance_check(today)
            log += rlog
            proposals.append(rprop)
        return log, proposals

    run_midnight = run_daily_update      # 이전 이름 호환

    def on_app_open(self, today: date) -> tuple:
        log = [f"📱 {today} 앱 실행"] + self._refresh(today)
        slog, prop = self._scan(today, "앱 실행")
        return log + slog, prop

    def on_payment_alert(self, tx: Transaction, today: date) -> tuple:
        threshold = min(LARGE_TX_MIN, LARGE_TX_RATIO * self.ledger.prev_essential)
        log = [f"💳 {today} 결제·출금 알림: {tx.description} {won(tx.amount)}"]
        if tx.kind != "출금" or tx.amount < threshold:
            self.ledger.add([tx])
            log.append(f"대형 거래 기준({won(threshold)}) 미만 → 기록만 하고 스캔 생략")
            return log, OrderProposal([], "스캔 생략")
        log.append(f"대형 거래(기준 {won(threshold)} 이상) → 즉시 트리거 스캔")
        self.ledger.add([tx])
        log += self._refresh(today)
        slog, prop = self._scan(today, "대형 출금·결제 알림")
        return log + slog, prop


# ════════════════════════════════════════════════════════════════════
# 종목 추천: ETF 중심 + 단계별 대체 규칙 (비슷한 ETF → 비중 이동 → 원할 때만 개별 상품)
# ════════════════════════════════════════════════════════════════════
@dataclass
class Product:
    ticker: str
    name: str
    asset_class: str
    kind: str                       # "ETF" / "해외상장 ETF" / "개별종목" / "개별채권"
    tags: tuple                     # 모델 포트폴리오 세부 항목과 매칭할 키워드
    price: float = 0.0
    expense_ratio: Optional[float] = None    # 총보수(%) — 증권사·운용사 데이터로 채움
    daily_trading_value: float = 0.0
    market_cap: float = 0.0
    dividend_yield: float = 0.0
    settlement_days: int = 2
    maturity_months: Optional[float] = None
    issuer: str = ""                # 개별 채권 발행사
    rating: str = ""                # 개별 채권 신용등급


# ETF 후보 목록 (예시) — 실제 운영 시 증권사·운용사 데이터로 가격·총보수·거래대금·상장 여부를 매일 갱신
ETF_CATALOG = [
    Product("360750", "TIGER 미국S&P500", FOR_EQ, "ETF", ("S&P500",)),
    Product("379800", "KODEX 미국S&P500TR", FOR_EQ, "ETF", ("S&P500",)),
    Product("133690", "TIGER 미국나스닥100", FOR_EQ, "ETF", ("나스닥",)),
    Product("379810", "KODEX 미국나스닥100TR", FOR_EQ, "ETF", ("나스닥",)),
    Product("458730", "TIGER 미국배당다우존스", FOR_EQ, "ETF", ("배당",)),
    Product("069500", "KODEX 200", DOM_EQ, "ETF", ("국내", "코스피")),
    Product("305080", "TIGER 미국채10년선물", IG_BOND, "ETF", ("국채", "장기", "중기"), maturity_months=120),
    Product("153130", "KODEX 단기채권", IG_BOND, "ETF", ("단기", "종합채권"), maturity_months=6),
    Product("411060", "ACE KRX금현물", COMMODITY, "ETF", ("금",)),
    Product("132030", "KODEX 골드선물(H)", COMMODITY, "ETF", ("금", "원자재")),
    Product("459580", "KODEX CD금리액티브(합성)", CASH, "ETF", ("현금", "파킹", "MMF", "CMA", "단기 자금", "대기")),
    # 해외 상장 ETF — 해외주식 계좌·환전 필요, 매매차익은 해외주식 양도세(250만 원 공제 후 22%) 대상
    Product("LQD", "iShares 투자등급 회사채 ETF", IG_BOND, "해외상장 ETF", ("회사채",), settlement_days=1),
    Product("HYG", "iShares 하이일드 회사채 ETF", HY_BOND, "해외상장 ETF", ("하이일드",), settlement_days=1),
]

# 1단계-② 성격이 비슷한 ETF를 찾을 때 쓰는 대체 키워드
SIMILAR_TAGS = {
    "회사채": ("종합채권", "크레딧", "채권혼합"),
    "하이일드": ("회사채", "크레딧"),
    "신흥국": ("글로벌", "선진국", "S&P500"),
    "테마": ("나스닥",),
    "혁신": ("나스닥",),
    "성장주": ("나스닥",),
    "REITs": ("리츠", "금"),
    "원자재": ("금",),
    "선진국": ("S&P500",),
}
# 2단계: 대체 ETF가 없을 때 비중을 옮길 더 안전한 곳 (같은 자산군 우선, 없으면 한 단계 안전한 자산군)
SAFER_CLASS = {HY_BOND: IG_BOND, IG_BOND: CASH, COMMODITY: IG_BOND, CRYPTO: CASH,
               FOR_EQ: IG_BOND, DOM_EQ: IG_BOND}
NO_RECOMMEND_CLASSES = {CRYPTO}      # 추천하지 않음: 사용자가 직접 보유 현황만 입력

ETF_MIN_TRADING_VALUE = 1_000_000_000      # 일 거래대금 10억 원 이상
STOCK_MIN_MARKET_CAP = 1_000_000_000_000   # 개별 종목: 시가총액 1조 원 이상
STOCK_MIN_TRADING_VALUE = 5_000_000_000    # 개별 종목: 일 거래대금 50억 원 이상
# 3단계 개별 채권 안전장치
RATING_ORDER = ["AAA", "AA+", "AA", "AA-", "A+", "A", "A-", "BBB+", "BBB", "BBB-", "BB+", "BB", "B", "CCC"]
BOND_MIN_RATING = "A"                      # 신용등급 A 이상
BOND_MIN_ISSUERS = 3                       # 발행사 3곳 이상으로 분산
BOND_MAX_ISSUER_SHARE = 1 / 3              # 한 발행사 비중 상한: 항목 비중의 1/3


def _ro(word: str) -> str:
    """'으로/로' 조사 선택"""
    ch = word[-1]
    if "가" <= ch <= "힣":
        jong = (ord(ch) - 0xAC00) % 28
        return word + ("로" if jong in (0, 8) else "으로")
    return word + "(으)로"


def _rating_ok(r: str) -> bool:
    return r in RATING_ORDER and RATING_ORDER.index(r) <= RATING_ORDER.index(BOND_MIN_RATING)


@dataclass
class ItemResolution:
    item: str
    asset_class: str
    weight: float
    step: str                      # "ETF" / "비슷한 ETF" / "개별 상품" / "비중 이동" / "추천 안 함"
    picks: list                    # [(Product, 설명)]
    moved_to: Optional[str] = None # 비중 이동 시 옮겨간 자산군
    note: str = ""


class ProductRecommender:
    """
    모델 포트폴리오 세부 항목별 종목 추천 — ETF 중심
    맞는 ETF가 없을 때 단계별 대체 규칙:
      1단계  ① 딱 맞는 국내 ETF → ② 딱 맞는 해외 상장 ETF(계좌·환전·세금 안내)
             → ③ 성격이 비슷한 ETF(국내 → 해외 상장)
      (사용자가 원할 때만) 개별 상품 — 안전장치를 통과할 때만
             · 주식: 시가총액 1조·일 거래대금 50억 원 이상
             · 채권: 신용등급 A 이상, 발행사 3곳 이상 분산, 한 발행사 비중 ≤ 항목 비중의 1/3
             · 하이일드 채권·가상자산: 개별 상품 추천 안 함
      2단계  그래도 없으면 비중을 더 안전한 곳으로 이동 (예: 회사채 → 국채, 하이일드 → 국채/우량채)
      가상자산은 추천하지 않고 비중을 현금성 자산으로 이동, 사용자가 직접 보유 현황만 입력
    기본(allow_individual=False)은 ETF만 추천
    """

    def __init__(self, etfs: Optional[list] = None, allow_individual: bool = False,
                 stock_universe: Optional[list] = None, bond_universe: Optional[list] = None):
        self.etfs = etfs if etfs is not None else ETF_CATALOG
        self.allow_individual = allow_individual
        self.stock_universe = stock_universe or []
        self.bond_universe = bond_universe or []

    # ── 1단계: ETF ────────────────────────────────────────────────
    def _etfs(self, item: str, cls: str, tags: Optional[tuple] = None, kind: str = "ETF") -> list:
        want = tags if tags is not None else None
        out = []
        for p in self.etfs:
            if p.asset_class != cls or p.kind != kind:
                continue
            if p.daily_trading_value and p.daily_trading_value < ETF_MIN_TRADING_VALUE:
                continue
            if (want is None and any(t in item for t in p.tags)) or \
                    (want is not None and any(t in p.tags for t in want)):
                out.append(p)
        return sorted(out, key=lambda p: (p.expense_ratio if p.expense_ratio is not None else 99,
                                          -p.daily_trading_value))

    def _similar_tags(self, item: str) -> tuple:
        tags = ()
        for key, sim in SIMILAR_TAGS.items():
            if key in item:
                tags += sim
        return tags

    # ── 개별 상품 (사용자가 원할 때만, 안전장치 통과 시) ─────────────
    def _individual(self, item: str, cls: str, weight: float, per_item: int) -> tuple:
        if cls in EQUITY_CLASSES:
            stocks = [p for p in self.stock_universe if p.asset_class == cls
                      and p.market_cap >= STOCK_MIN_MARKET_CAP
                      and p.daily_trading_value >= STOCK_MIN_TRADING_VALUE
                      and (not p.tags or any(t in item for t in p.tags))]
            key = (lambda p: -p.dividend_yield) if "배당" in item else (lambda p: -p.market_cap)
            return [(p, "개별종목(사용자 요청)") for p in sorted(stocks, key=key)[:per_item]], ""
        if cls == IG_BOND:
            ok = [b for b in self.bond_universe if b.asset_class == IG_BOND and _rating_ok(b.rating)]
            by_issuer = {}
            for b in sorted(ok, key=lambda b: RATING_ORDER.index(b.rating)):
                by_issuer.setdefault(b.issuer, b)
            if len(by_issuer) < BOND_MIN_ISSUERS:
                return [], (f"개별 채권 안전장치 미충족: 등급 {BOND_MIN_RATING} 이상 발행사 "
                            f"{len(by_issuer)}곳 < {BOND_MIN_ISSUERS}곳")
            cap = weight * BOND_MAX_ISSUER_SHARE
            picks = [(b, f"개별채권 {b.rating}, 발행사당 최대 {cap:.1f}%")
                     for b in list(by_issuer.values())[:max(BOND_MIN_ISSUERS, per_item)]]
            return picks, ""
        return [], "이 자산군은 개별 상품을 추천하지 않음"

    # ── 항목별 해석 ───────────────────────────────────────────────
    def resolve(self, model: ModelPortfolio, per_item: int = 2) -> list:
        out = []
        for item, cls, w in model.items:
            if cls in NO_RECOMMEND_CLASSES:
                out.append(ItemResolution(item, cls, w, "추천 안 함", [], SAFER_CLASS[cls],
                                          "가상자산은 추천하지 않음 → 비중을 현금성자산으로 이동 "
                                          "(직접 보유 시 보유 현황만 입력)"))
                continue
            picks = self._etfs(item, cls)
            if picks:
                out.append(ItemResolution(item, cls, w, "ETF", [(p, "ETF") for p in picks[:per_item]]))
                continue
            picks = self._etfs(item, cls, kind="해외상장 ETF")
            if picks:
                out.append(ItemResolution(item, cls, w, "ETF", [(p, "해외상장 ETF") for p in picks[:per_item]],
                                          note="해외주식 계좌·환전 필요, 매매차익 해외주식 양도세 대상"))
                continue
            sim = self._similar_tags(item)
            picks = self._etfs(item, cls, tags=sim) if sim else []
            if picks:
                out.append(ItemResolution(item, cls, w, "비슷한 ETF",
                                          [(p, "비슷한 ETF") for p in picks[:per_item]],
                                          note=f"딱 맞는 ETF 없음 → 성격이 비슷한 ETF로 대체"))
                continue
            picks = self._etfs(item, cls, tags=sim, kind="해외상장 ETF") if sim else []
            if picks:
                out.append(ItemResolution(item, cls, w, "비슷한 ETF",
                                          [(p, "비슷한 해외상장 ETF") for p in picks[:per_item]],
                                          note="딱 맞는 ETF 없음 → 비슷한 해외 상장 ETF (계좌·환전·세금 안내)"))
                continue
            if self.allow_individual:
                picks, why = self._individual(item, cls, w, per_item)
                if picks:
                    out.append(ItemResolution(item, cls, w, "개별 상품", picks,
                                              note="ETF 없음 → 사용자 요청에 따라 개별 상품 (안전장치 통과)"))
                    continue
            else:
                why = ""
            out.append(ItemResolution(item, cls, w, "비중 이동", [], None,
                                      f"대체 ETF 없음{' · ' + why if why else ''}"))
        # 2단계 비중 이동: 같은 자산군에 추천 종목이 있는 다른 항목 → 없으면 한 단계 안전한 자산군
        for r in out:
            if r.step != "비중 이동":
                continue
            same = [x for x in out if x is not r and x.asset_class == r.asset_class and x.picks]
            if same:
                tgt = max(same, key=lambda x: x.weight)
                r.moved_to = r.asset_class
                r.note += f" → {r.weight:.0f}%를 같은 자산군 '{tgt.item}' 항목({tgt.picks[0][0].name})으로 편입"
            else:
                r.moved_to = SAFER_CLASS.get(r.asset_class, CASH)
                r.note += f" → {r.weight:.0f}%를 더 안전한 {_ro(r.moved_to)} 편입"
        return out

    def effective_targets(self, model: ModelPortfolio) -> dict:
        """비중 이동을 반영한 실제 목표 비중 (자산군 합계 100%)"""
        t = {c: 0.0 for c in ASSET_CLASSES}
        for r in self.resolve(model):
            t[r.moved_to or r.asset_class] += r.weight
        return t

    def recommend(self, model: ModelPortfolio, per_item: int = 2) -> dict:
        return {(r.item, r.asset_class, r.weight): r.picks for r in self.resolve(model, per_item)}

    def report(self, model: ModelPortfolio, per_item: int = 2) -> list:
        lines = [f"{model.name} 추천 종목 ({'ETF + 개별 상품(요청)' if self.allow_individual else 'ETF 중심'})"]
        for r in self.resolve(model, per_item):
            names = ", ".join(f"{p.name}({p.ticker}) [{d}]" for p, d in r.picks) or "-"
            lines.append(f"  · {r.item} {r.weight:.0f}% ({r.asset_class}) [{r.step}]: {names}")
            if r.note:
                lines.append(f"      ↳ {r.note}")
        return lines

    def instruments(self, model: ModelPortfolio) -> dict:
        """자산군별 대표 매수 종목: 비중이 가장 큰 세부 항목의 1순위 추천 종목"""
        best = {}
        for r in self.resolve(model, per_item=1):
            if r.picks and (r.asset_class not in best or r.weight > best[r.asset_class][0]):
                p = r.picks[0][0]
                best[r.asset_class] = (r.weight, Instrument(
                    p.ticker, p.name, r.asset_class, p.price or 1.0, p.settlement_days,
                    daily_trading_value=p.daily_trading_value or math.inf,
                    overseas=p.kind == "해외상장 ETF", tax_rate=0.22 if p.kind == "해외상장 ETF" else 0.0,
                    maturity_months=p.maturity_months))
        return {c: v[1] for c, v in best.items()}


# ════════════════════════════════════════════════════════════════════
# 데모
# ════════════════════════════════════════════════════════════════════
def demo_instruments() -> dict:
    return {
        DOM_EQ: Instrument("069500", "KODEX 200", DOM_EQ, 38_000, daily_trading_value=5e11),
        FOR_EQ: Instrument("360750", "TIGER 미국S&P500", FOR_EQ, 21_000, daily_trading_value=3e11),
        IG_BOND: Instrument("305080", "TIGER 미국채10년선물", IG_BOND, 11_500, daily_trading_value=2e10,
                            maturity_months=120),
        SHORT_BOND_KEY: Instrument("ST-BOND", "단기국채 ETF(만기 3개월 미만, 예시)", IG_BOND, 100_000,
                                   settlement_days=1, daily_trading_value=5e10, maturity_months=2),
        HY_BOND: Instrument("HYG-K", "하이일드채권 ETF", HY_BOND, 9_800, daily_trading_value=2e9),
        COMMODITY: Instrument("411060", "ACE KRX금현물", COMMODITY, 18_000, daily_trading_value=3e10),
        CRYPTO: Instrument("BTC-ETF", "비트코인 현물 ETF", CRYPTO, 60_000, daily_trading_value=5e10),
        CASH: Instrument("CMA", "CMA/파킹통장", CASH, 1.0, settlement_days=0),
    }


def _hr(title: str):
    print("\n" + "═" * 70 + f"\n {title}\n" + "═" * 70)


def main():
    inst = demo_instruments()

    _hr("STAGE 1. 재무 체력 측정")
    profile = FinancialProfile(
        monthly_fixed_income=4_000_000, essential_expense=2_600_000, cash_current=12_000_000,
        income_type=IncomeType.REGULAR, monthly_debt_payment=700_000, m_multiplier=4)
    print(profile.summary())

    _hr("STAGE 2. 위험 성향 산출")
    survey = SurveyAnswers(q1_1=50, q1_2=66, q1_3=66, q2_1=75, q2_2=66)
    risk = assess_risk(survey, profile.buffer)
    print(risk.summary())
    model = MODEL_PORTFOLIOS[risk.tier]
    print(f"  모델 포트폴리오: {model.name} — {model.purpose}")
    for n, c, w in model.items:
        print(f"    · {n:<24}{c:<10}{w:>5.0f}%")

    _hr("STAGE 3 경로 A. 신규 투자자 빌드업 (3회 분할 매수 + 구축 중 트리거)")
    bprof = FinancialProfile(
        monthly_fixed_income=4_000_000, essential_expense=2_600_000, cash_current=12_000_000,
        income_type=IncomeType.REGULAR, monthly_debt_payment=700_000, m_multiplier=4)
    bm = BuildUpManager(bprof, survey, inst, data_link=DataLink.MANUAL)   # 가계부 직접 입력 사용자
    print(f"  투자 대기 현금 = {won(bprof.cash_current)} - 비상금 {won(bprof.c_reserve)} = {won(bm.pending_cash)}")
    build_scenarios = [
        ("1개월: 평시", LedgerSnapshot(4_000_000, 2_600_000, 10_400_000)),
        ("2개월: 필수 지출 급증 (B-2)", LedgerSnapshot(4_000_000, 3_300_000, 13_500_000)),
        ("3개월: 20일 뒤 목돈 지출 1,600만 원 (C)", LedgerSnapshot(4_000_000, 3_300_000, 13_500_000,
                                                          upcoming_cf=16_000_000, dday=20)),
        ("4개월: 잉여율 회복", LedgerSnapshot(4_000_000, 2_650_000, 14_000_000)),
        ("5개월: 평시", LedgerSnapshot(4_000_000, 2_600_000, 14_000_000)),
    ]
    for title, snap in build_scenarios:
        if bm.completed:
            break
        print(f"\n  ■ {title}")
        log, proposal = bm.monthly_step(snap)
        for line in log:
            print("   - " + line)
        if proposal.orders:
            print(proposal.render(bm.portfolio))
        print("   - 전환 판정: " + bm.confirm(proposal))
    print()
    print(bm.portfolio.report(bm.targets))
    print(f"  전환 가능: {bm.completed} → 가능 시 bm.to_manager()로 정식 관리 모드 이관")

    print("\n  ▶ 직접 입력 사용자 가계부 미입력 알림 · 2개월 연속 미입력 시 신규 매수 중단")
    mgr_a = bm.to_manager()
    mgr_a.notify = lambda n: print("    " + str(n))
    mgr_a.last_ledger_period = "2026-08"          # 8월 가계부까지 입력된 상태
    for d in [date(2026, 10, 2), date(2026, 10, 6), date(2026, 11, 6)]:
        print(f"   · {d} 확인")
        mgr_a.check_ledger_input(d)
        print(f"     신규 매수 중단: {mgr_a.ledger_frozen}")
    print("   · 9월 가계부만 뒤늦게 입력 (최근 마감 월 10월은 아직 미입력)")
    log, prop = mgr_a.monthly_cycle(LedgerSnapshot(4_000_000, 2_600_000, period="2026-09"))
    print("     " + log[0]); print("     " + [l for l in log if "동결" in l][0])
    res = execute_with_approval(prop, MockBroker(), lambda p: True, datetime(2026, 11, 9, 11, 0),
                                buy_frozen=mgr_a.buy_frozen)
    print("     발주:", res[:2])
    mgr_a.confirm(prop)
    print("   · 10월 가계부 입력")
    log, prop = mgr_a.monthly_cycle(LedgerSnapshot(4_000_000, 2_600_000, period="2026-10"))
    print(f"     신규 매수 중단: {mgr_a.ledger_frozen} / 매매 제안 {len(prop.orders)}건")

    _hr("STAGE 3 경로 B. 기존 보유자 전환")
    existing = Portfolio([
        Holding("005930", "삼성전자", DOM_EQ, 150, 70_000, 60_000, volatility=30, product_type="주식"),
        Holding("035720", "카카오", DOM_EQ, 60, 40_000, 55_000, volatility=40, product_type="주식"),
        Holding("005380", "현대차", DOM_EQ, 10, 200_000, 180_000, volatility=30, locked=True, product_type="주식"),
        Holding("NVDA", "엔비디아", FOR_EQ, 120, 180_000, 60_000, volatility=50,
                tax_rate=0.22, overseas=True, settlement_days=1),
        Holding("TSLA", "테슬라", FOR_EQ, 30, 300_000, 420_000, volatility=60,
                tax_rate=0.22, overseas=True, settlement_days=1),
        Holding("360750", "TIGER 미국S&P500", FOR_EQ, 200, 21_000, 18_000, volatility=18,
                account="ISA", daily_trading_value=3e11),
        Holding("BTC", "비트코인", CRYPTO, 0.05, 140_000_000, 160_000_000, volatility=70, settlement_days=0),
        Holding("CMA", "CMA/파킹통장", CASH, 1_000_000, 1.0, settlement_days=0),
    ])
    targets = model.targets
    print(existing.report(targets))

    print("\n  ▶ 전략 A: 즉시 리밸런싱 (트리거 대응 포함)")
    aprof = FinancialProfile(
        monthly_fixed_income=4_000_000, essential_expense=2_600_000, cash_current=12_000_000,
        income_type=IncomeType.REGULAR, monthly_debt_payment=700_000, m_multiplier=4)
    am = StrategyAManager(aprof, survey, copy.deepcopy(existing), inst)
    a_scenarios = [
        ("1회차: 20일 뒤 목돈 지출 1,500만 원 (Trigger C)",
         LedgerSnapshot(4_000_000, 2_600_000, 12_000_000, upcoming_cf=15_000_000, dday=20)),
        ("2회차: 지출 완료, 평시 복귀", LedgerSnapshot(4_000_000, 2_600_000, 12_000_000)),
    ]
    for title, snap in a_scenarios:
        print(f"\n  ■ {title}")
        log, proposal = am.step(snap)
        for line in log:
            print("   - " + line)
        print(proposal.render(am.portfolio))
        res = execute_with_approval(proposal, MockBroker(), lambda p: True, datetime(2026, 9, 24, 11, 0))
        print("     → 사용자 승인 후 발주 (" + str(len(res)) + "건)")
        print("   - 전환 판정: " + am.confirm(proposal))
        if am.completed:
            break
    adj = locked_adjusted_targets(am.portfolio, am.targets)
    print(am.portfolio.report(adj))
    ok, bad = precision_check(am.portfolio, am.targets)
    print(f"  정밀도 검증(±1%p, 고정 자산 반영): {'통과' if ok else '미달 ' + str({k: round(v, 2) for k, v in bad.items()})}")

    print("\n  ▶ 전략 B: 점진적 리밸런싱 (손실 자산 유예·희석 + 트리거 대응)")
    bm_prof = FinancialProfile(
        monthly_fixed_income=4_000_000, essential_expense=2_600_000, cash_current=12_000_000,
        income_type=IncomeType.REGULAR, monthly_debt_payment=700_000, m_multiplier=4)
    sb = StrategyBManager(bm_prof, survey, copy.deepcopy(existing), inst)
    for line in sb.analysis_report():
        print("   · " + line)
    b_scenarios = [
        ("1개월: 1차 매매", LedgerSnapshot(4_000_000, 2_600_000, 12_000_000)),
        ("2개월: 필수 지출 급증 (Trigger B-2)", LedgerSnapshot(4_000_000, 3_300_000, 13_500_000)),
        ("3개월: 잉여율 회복 + 유예 자산 일부 회복", LedgerSnapshot(4_000_000, 2_600_000, 13_500_000)),
        ("4개월: 평시", LedgerSnapshot(4_000_000, 2_600_000, 13_500_000)),
    ]
    for i, (title, snap) in enumerate(b_scenarios):
        if i == 2:   # 시장 회복 가정: 테슬라 -3%, 비트코인 본전 이상
            sb.portfolio.find("TSLA").price = 407_000
            sb.portfolio.find("BTC").price = 165_000_000
        print(f"\n  ■ {title}")
        log, proposal = sb.step(snap)
        for line in log:
            print("   - " + line)
        if proposal.orders:
            print(proposal.render(sb.portfolio))
        print("   - 전환 판정: " + sb.confirm(proposal))
        if sb.completed:
            break
    print(sb.portfolio.report(locked_adjusted_targets(sb.portfolio, sb.targets)))
    after = sb.portfolio

    _hr("가계부 연동 데이터 — 가맹점 단위 분류 · 사용자 확인 · 비상금 이체 자동 반영")
    clf = LedgerClassifier(emergency_accounts={"ACC-EMG"})
    sep = [
        Transaction("T01", date(2026, 9, 25), "(주)한빛 급여", 4_000_000, "입금"),
        Transaction("T02", date(2026, 9, 10), "예금 이자", 12_000, "입금"),
        Transaction("T03", date(2026, 9, 1), "월세 자동이체", 900_000, "출금"),
        Transaction("T04", date(2026, 9, 5), "신용대출 원리금", 700_000, "출금"),
        Transaction("T05", date(2026, 9, 15), "한국전력 전기요금", 60_000, "출금"),
        Transaction("T06", date(2026, 9, 20), "OO생명 보험료", 150_000, "출금"),
        Transaction("T07", date(2026, 9, 7), "㈜이마트 역삼점 결제", 420_000, "출금"),
        Transaction("T08", date(2026, 9, 12), "KCP*쿠팡 09/12", 60_000, "출금", biz_no="120-88-00767"),
        Transaction("T09", date(2026, 9, 19), "쿠팡(주) 로켓배송", 350_000, "출금", biz_no="120-88-00767"),
        Transaction("T10", date(2026, 9, 22), "OO태권도장 2호점", 150_000, "출금", card_merchant_id="C-5521"),
        Transaction("T11", date(2026, 9, 26), "비상금 적립", 500_000, "출금", counterparty="ACC-EMG"),
        Transaction("T12", date(2026, 9, 28), "비상금 통장에서 이체", 200_000, "입금", counterparty="ACC-EMG"),
    ]
    rv = MonthlyLedgerReview("2026-09", sep, clf)
    print("  [9월 자동 분류]")
    for it in rv.items.values():
        print("    " + str(it))
    print("  [사용자 수정]")
    print("    " + str(rv.set("T08", True, SCOPE_AMOUNT, "생필품(필수)", amount_max=100_000)))
    print("    " + str(rv.set("T09", False, SCOPE_ONCE, "가전 구매(비필수)")))
    print("    " + str(rv.set("T10", True, SCOPE_MERCHANT, "아이 태권도장(보육)")))
    rv.confirm_all()
    for line in rv.summary():
        print("  " + line)
    snap_sep = rv.to_snapshot(emergency_balance=12_000_000)

    oct_tx = [Transaction("O01", date(2026, 10, 25), "(주)한빛 급여", 4_000_000, "입금"),
              Transaction("O06", date(2026, 10, 1), "월세 자동이체", 900_000, "출금"),
              Transaction("O07", date(2026, 10, 5), "신용대출 원리금", 700_000, "출금"),
              Transaction("O08", date(2026, 10, 20), "OO생명 보험료", 150_000, "출금"),
              Transaction("O09", date(2026, 10, 8), "이마트 강남점", 400_000, "출금"),
              Transaction("O02", date(2026, 10, 9), "COUPANG 결제", 45_000, "출금"),
              Transaction("O03", date(2026, 10, 18), "쿠팡 가전", 280_000, "출금", biz_no="120-88-00767"),
              Transaction("O04", date(2026, 10, 22), "OO태권도장 본점", 150_000, "출금", card_merchant_id="C-5521"),
              Transaction("O05", date(2026, 10, 26), "비상금 적립", 500_000, "출금", counterparty="ACC-EMG")]
    rv2 = MonthlyLedgerReview("2026-10", oct_tx, clf)
    print("  [10월: 가맹점 규칙 자동 적용]")
    for it in rv2.items.values():
        print("    " + str(it))
    rv2.confirm_all()
    snap_oct = rv2.to_snapshot()       # 잔액 미입력 → 9월 잔액 + 비상금 입금 − 출금으로 자동 계산
    nov_tx = [Transaction("N01", date(2026, 11, 25), "(주)한빛 급여", 4_000_000, "입금"),
              Transaction("N02", date(2026, 11, 1), "월세 자동이체", 900_000, "출금"),
              Transaction("N03", date(2026, 11, 5), "신용대출 원리금", 700_000, "출금"),
              Transaction("N07", date(2026, 11, 20), "OO생명 보험료", 150_000, "출금"),
              Transaction("N08", date(2026, 11, 9), "홈플러스 결제", 430_000, "출금"),
              Transaction("N09", date(2026, 11, 15), "한국전력 전기요금", 70_000, "출금"),
              Transaction("N04", date(2026, 11, 26), "비상금 적립", 500_000, "출금", counterparty="ACC-EMG"),
              Transaction("N05", date(2026, 11, 26), "주거래통장에서 입금", 500_000, "입금", account="ACC-EMG"),
              Transaction("N06", date(2026, 11, 30), "파킹통장 이자", 21_000, "입금", account="ACC-EMG")]
    rv3 = MonthlyLedgerReview("2026-11", nov_tx, clf,
                              account_balances={"ACC-MAIN": 3_200_000, "ACC-EMG": 13_021_000})
    print("  [11월: 비상금 계좌 마이데이터 연동 → 연동 잔액 사용]")
    for it in [rv3.items[k] for k in ('N04', 'N05', 'N06')]:
        print("    " + str(it))
    rv3.confirm_all()
    for line in rv3.summary():
        print("  " + line)
    snap_nov = rv3.to_snapshot()
    print("  [연 1회 규칙 점검]", clf.rules_to_review("2027-05") or "점검 대상 없음")

    print("\n  [직접 입력 사용자 — 보유 종목은 증권사 API로 자동 수집]")
    pm = PortfolioManager(FinancialProfile(4_000_000, 2_600_000, 12_000_000, IncomeType.REGULAR, m_multiplier=4),
                          survey, Portfolio([Holding("305080", "TIGER 미국채10년선물", IG_BOND, 300, 11_500,
                                                     maturity_months=120, locked=True)]),
                          inst, data_link=DataLink.MANUAL)
    api = MockBrokerData([
        Holding("305080", "TIGER 미국채10년선물", IG_BOND, 320, 11_600, 11_450),
        Holding("360750", "TIGER 미국S&P500", FOR_EQ, 150, 21_000, 19_000),
    ])
    for n in pm.sync_holdings(api):
        print("    " + n)
    b = pm.portfolio.find("305080")
    print(f"    유지된 사용자 설정: 매도 금지={b.locked}, 잔존만기={b.maturity_months}개월")
    log, _ = pm.monthly_cycle(snap_sep)
    print("    9월: " + log[0])
    log, _ = pm.monthly_cycle(snap_oct)
    print("    10월: " + log[0])
    log, _ = pm.monthly_cycle(snap_nov)
    print("    11월: " + log[0])

    _hr("가계부 연동 관리 모드 — 매일 07:00 업데이트 · 앱 실행 · 대형 결제 알림 스캔")
    live_mgr = PortfolioManager(
        FinancialProfile(4_000_000, 2_600_000, 12_000_000, IncomeType.REGULAR, m_multiplier=4), survey,
        Portfolio([Holding("360750", "TIGER 미국S&P500", FOR_EQ, 700, 21_000, 18_000, account="ISA"),
                   Holding("305080", "TIGER 미국채10년선물", IG_BOND, 900, 11_500, 11_000, maturity_months=120),
                   Holding("411060", "ACE KRX금현물", COMMODITY, 160, 18_000, 17_000),
                   Holding("CMA", "CMA/파킹통장", CASH, 1_500_000, 1.0, settlement_days=0)]), inst)
    live_mgr.last_emergency_balance = 12_000_000
    lclf = LedgerClassifier(emergency_accounts={"ACC-EMG"})
    ledger = LiveLedger("2026-11", lclf, prev_income=4_000_000, prev_essential=2_600_000)
    car = Transaction("L05", date(2026, 11, 12), "OO자동차정비 결제", 4_200_000, "출금", account="ACC-EMG")
    md = MockMyData(
        [Transaction("L01", date(2026, 11, 1), "월세 자동이체", 900_000, "출금"),
         Transaction("L02", date(2026, 11, 5), "신용대출 원리금", 700_000, "출금"),
         Transaction("L03", date(2026, 11, 9), "이마트 결제", 420_000, "출금"),
         Transaction("L04", date(2026, 11, 10), "스타벅스", 6_500, "출금"),
         car,
         Transaction("L06", date(2026, 11, 25), "(주)한빛 급여", 4_000_000, "입금"),
         Transaction("L07", date(2026, 11, 20), "OO생명 보험료", 150_000, "출금"),
         Transaction("L08", date(2026, 11, 26), "비상금 적립", 1_400_000, "출금", counterparty="ACC-EMG")],
        [(date(2026, 11, 1), {"ACC-EMG": 12_000_000}),
         (date(2026, 11, 12), {"ACC-EMG": 7_800_000}),
         (date(2026, 11, 26), {"ACC-EMG": 9_200_000})])
    broker = MockBrokerData(lambda: live_mgr.portfolio.holdings)
    op = LiveOperation(live_mgr, ledger, md, broker, start=date(2026, 10, 31))

    def show(res):
        log, props = res
        for line in log:
            print("   " + line)
        for pr in (props if isinstance(props, list) else [props]):
            if pr.orders:
                print(pr.render(live_mgr.portfolio))
                live_mgr.confirm(pr)

    show(op.run_daily_update(date(2026, 11, 6)))
    show(op.on_app_open(date(2026, 11, 10)))
    show(op.on_payment_alert(Transaction("L04b", date(2026, 11, 10), "스타벅스", 6_500, "출금"), date(2026, 11, 10)))
    show(op.on_payment_alert(car, date(2026, 11, 12)))
    show(op.on_app_open(date(2026, 11, 12)))                     # 같은 날 재실행 → 중복 대응 없음
    ledger.register_event("이사 잔금", 15_000_000, date(2026, 12, 5))
    show(op.on_app_open(date(2026, 11, 15)))
    show(op.run_daily_update(date(2026, 12, 1)))

    _hr("발주 직전 점검 — 현재가·예수금 확인 후 수량 조정")
    prop = OrderProposal([
        Order("매수", "360750", "TIGER 미국S&P500", FOR_EQ, 100, 21_000, 0, "스마트 바이"),
        Order("매수", "305080", "TIGER 미국채10년선물", IG_BOND, 200, 11_500, 0, "스마트 바이"),
        Order("매수", "411060", "ACE KRX금현물", COMMODITY, 50, 18_000, 0, "스마트 바이"),
        Order("매도", "005930", "삼성전자", DOM_EQ, 30, 70_000, 0, "Trigger C 현금화", PURPOSE_LIQUIDITY),
    ], "07:00 생성 매매 제안")
    print(prop.render(Portfolio()))
    brk = MockBroker(quotes={"360750": 21_400, "305080": 11_450, "411060": 18_900, "005930": 68_500},
                     deposit=4_000_000)
    print("  ▶ 10:30 장중 발주 (현재가·예수금 확인)")
    held_pf = Portfolio([
        Holding("005930", "삼성전자", DOM_EQ, 30, 70_000, 60_000, volatility=30, product_type="주식"),
        Holding("305080", "TIGER 미국채10년선물", IG_BOND, 400, 11_450, 11_000, volatility=8, maturity_months=120),
        Holding("TSLA", "테슬라", FOR_EQ, 10, 300_000, 420_000, volatility=60, overseas=True, settlement_days=1),
        Holding("069500", "KODEX 200", DOM_EQ, 50, 38_000, 35_000, volatility=20),
        Holding("005380", "현대차", DOM_EQ, 10, 200_000, 180_000, volatility=30, locked=True, product_type="주식"),
    ])
    for r in execute_with_approval(prop, brk, lambda p: True, datetime(2026, 12, 2, 10, 30), portfolio=held_pf,
                                   push=lambda n: print("    " + str(n))):
        print("    → " + r)
    print("  ▶ 10:42 사용자가 푸시에서 대체 매도 승인")
    res, done = execute_pending_substitutes(prop, brk, datetime(2026, 12, 2, 10, 42), held_pf)
    for r in res:
        print("    → " + r)
    print("  ▶ 보류(재승인 필요):", [o.name for o in prop.held])
    print("  ▶ T+2 예약 매수 발주 (정산 후 예수금 150만 원)")
    res, _ = execute_scheduled([Order("매수", "360750", "TIGER 미국S&P500", FOR_EQ, 90, 21_000, 2, "밴드 리밸런싱 매수")],
                               MockBroker(quotes={"360750": 21_300}, deposit=1_500_000), datetime(2026, 12, 4, 10, 5))
    for r in res:
        print("    → " + r)

    _hr("데이터 제어 — 연동 제외 · 식별 정보 암호화 · 오프라인 현금 · 사용자 수정")
    ctl = DataControl(IdVault(b"demo-secret-key-please-use-KMS"))
    t_main = ctl.register_account("110-234-567890", "OO은행", "입출금", "주거래")
    t_emg = ctl.register_account("356-11-2233445", "OO증권", "CMA", "비상금", emergency=True)
    t_sub = ctl.register_account("620-99-887766", "OO은행", "청약", "주택청약", excluded=True)
    for line in ctl.account_list():
        print("    " + line)
    print(f"    저장된 식별값 예: {t_main} (원본 번호는 저장하지 않음)")
    raw_tx = [Transaction("D01", date(2026, 12, 3), "월세 자동이체", 900_000, "출금", account="110-234-567890"),
              Transaction("D02", date(2026, 12, 5), "주택청약 납입", 200_000, "출금", account="110-234-567890",
                          counterparty="620-99-887766"),
              Transaction("D03", date(2026, 12, 5), "청약 입금", 200_000, "입금", account="620-99-887766")]
    md2 = ControlledMyData(MockMyData(raw_tx, [(date(2026, 12, 1), {"110-234-567890": 3_000_000,
                                                                     "356-11-2233445": 9_000_000,
                                                                     "620-99-887766": 15_000_000})]), ctl)
    txs = md2.fetch_transactions(date(2026, 11, 30), date(2026, 12, 6))
    print(f"    수집 거래 {len(txs)}건 (연동 제외 계좌의 거래 제외), 잔액 계좌 {len(md2.fetch_balances(date(2026, 12, 6)))}개")
    ctl.set_offline_cash("집 금고 현금", 500_000)
    lg = LiveLedger("2026-12", LedgerClassifier(), 4_000_000, 2_600_000, control=ctl)
    lg.add(txs)
    lg.balances = md2.fetch_balances(date(2026, 12, 6))
    for it in lg.review().items.values():
        print("    " + str(it))
    snap_c = lg.live_snapshot(date(2026, 12, 6), 0)
    print(f"    비상금 계좌 잔액 {won(snap_c.c_current)} ({snap_c.balance_source})")
    ctl.override("2026-12", "essential_expense", 2_800_000, "연말 경조사 반영", auto_value=snap_c.essential_expense)
    snap_c = lg.live_snapshot(date(2026, 12, 6), 0)
    print(f"    사용자 수정 후 필수 지출 {won(snap_c.essential_expense)}")
    ctl.override_holding("360750", quantity=650, reason="장외 이전분 반영")
    print(f"    증권사 700주 → 사용자 수정 반영: "
          f"{ControlledBrokerData(MockBrokerData([Holding('360750', 'TIGER 미국S&P500', FOR_EQ, 700, 21_000)]), ctl).fetch_holdings()[0].quantity}주")
    print("    변경 이력:")
    for a in ctl.audit[-3:]:
        print(f"      {a}")

    print("  [계좌번호 원본 보기 — 비밀번호 확인 후 30초 표시]")
    clock = {"now": datetime(2026, 12, 6, 9, 0, 0)}
    tick = lambda: clock["now"]
    ctl2 = DataControl(IdVault(b"demo-secret-key-please-use-KMS"),
                       AccountSecretStore("my-pin-2580", clock=tick))
    tok = ctl2.register_account("110-234-567890", "OO은행", "입출금", "주거래", transfer_token="OB-FT-000123")
    print(f"    화면 기본 표시: {ctl2.accounts[tok].masked} / 자동 이체는 금융사 토큰 {ctl2.accounts[tok].transfer_token} 사용")
    for pw in ["000000", "my-pin-2580"]:
        try:
            shown = ctl2.reveal_account(tok, pw)
            print(f"    비밀번호 확인 → 원본: {shown}")
        except PermissionError as e:
            print(f"    {e}")
    clock["now"] += timedelta(seconds=31)
    print(f"    31초 후 표시: {shown}")
    for _ in range(5):
        try:
            ctl2.reveal_account(tok, "wrong-pin")
        except PermissionError as e:
            last = str(e)
    print(f"    5회 연속 실패: {last}")
    try:
        ctl2.reveal_account(tok, "my-pin-2580")
    except PermissionError as e:
        print(f"    잠금 중 올바른 비밀번호: {e}")
    clock["now"] += timedelta(minutes=11)
    ctl2.secrets.change_secret("my-pin-2580", "new-pin-7777")
    print(f"    잠금 해제 후 비밀번호 변경 → 새 비밀번호로 조회: {ctl2.reveal_account(tok, 'new-pin-7777')}")
    print("    조회 기록:")
    for a in ctl2.secrets.access_log:
        print(f"      {a}")

    _hr("실시간 평가 → Current_Ratio_i · 순잉여금 → 스마트 바이 · 기계적 리밸런싱")
    vctl = DataControl(IdVault(b"demo-secret-key-please-use-KMS"))
    vctl.register_account("110-234-567890", "OO은행", "입출금", "생활비")
    vctl.register_account("356-11-2233445", "OO증권", "CMA", "비상금", emergency=True)
    vctl.register_account("777-88-999000", "OO은행", "파킹통장", "투자 대기")
    vctl.register_account("620-99-887766", "OO은행", "청약", "주택청약", excluded=True)
    vmd = MockMyData([], [(date(2026, 12, 1), {"110-234-567890": 2_500_000, "356-11-2233445": 10_400_000,
                                               "777-88-999000": 1_200_000, "620-99-887766": 15_000_000})])
    vbroker = MockBrokerData([Holding("360750", "TIGER 미국S&P500", FOR_EQ, 700, 21_000, 18_000, account="ISA"),
                              Holding("305080", "TIGER 미국채10년선물", IG_BOND, 900, 11_500, 11_000),
                              Holding("411060", "ACE KRX금현물", COMMODITY, 160, 18_000, 17_000)])
    vquote = MockBroker(quotes={"360750": 21_300, "305080": 11_420, "411060": 18_150})
    val = RealtimeValuation(vbroker, vquote, vmd, vctl).scan(datetime(2026, 12, 2, 10, 15))
    tgt3 = MODEL_PORTFOLIOS[3].targets
    for line in val.sources + val.report(tgt3):
        print("  " + line)

    vm = PortfolioManager(FinancialProfile(4_000_000, 2_600_000, 10_400_000, IncomeType.REGULAR, m_multiplier=4),
                          survey, val.portfolio, inst)
    vm.refresh_valuation(val)
    nov = MonthlyLedgerReview("2026-11", [
        Transaction("V01", date(2026, 11, 25), "(주)한빛 급여", 4_000_000, "입금"),
        Transaction("V02", date(2026, 11, 1), "월세 자동이체", 900_000, "출금"),
        Transaction("V03", date(2026, 11, 5), "신용대출 원리금", 700_000, "출금"),
        Transaction("V04", date(2026, 11, 9), "홈플러스 결제", 450_000, "출금"),
        Transaction("V05", date(2026, 11, 20), "OO생명 보험료", 150_000, "출금"),
        Transaction("V06", date(2026, 11, 18), "CGV 영화", 60_000, "출금"),
        Transaction("V07", date(2026, 11, 23), "백화점 의류", 340_000, "출금"),
    ], LedgerClassifier())
    nov.confirm_all()
    print("  " + nov.summary()[0])
    log, prop = vm.monthly_cycle(nov.to_snapshot(emergency_balance=10_400_000))
    for line in log:
        if "Free_Cash" in line or "스마트 바이" in line or line.startswith("  ") or "기계적" in line or "이탈" in line:
            print("   " + line)
    print(prop.render(vm.portfolio))

    print("  [계절성·비정기 지출 대비 — 달력 연동 + 1년치 지출 패턴]")
    kcal = KoreanCalendar(provider=None)       # 실제: KoreanCalendar(DataGoKrHolidayAPI(인증키))
    kcal.add_user_event(date(2027, 2, 3), "부모님 설 선물·세뱃돈", 1_200_000)
    kcal.add_user_event(date(2027, 3, 20), "자동차 보험 갱신", 900_000)
    kcal.add_user_event(date(2027, 4, 30), "전세 보증금 증액", 15_000_000, big=True)
    for y in (2026, 2027, 2028):
        kcal.holidays(y)
        print(f"    {y}년 공휴일·명절 출처: {kcal.sources[y]}")
    for line in kcal.text_month(2027, 2):
        print("    " + line)
    hist = [("2025-10", 3_800_000), ("2025-11", 2_600_000), ("2025-12", 2_950_000), ("2026-01", 2_650_000),
            ("2026-02", 3_300_000), ("2026-03", 2_600_000), ("2026-04", 2_650_000), ("2026-05", 3_600_000),
            ("2026-06", 2_600_000), ("2026-07", 2_700_000), ("2026-08", 2_650_000), ("2026-09", 3_900_000)]
    vm.seasonal = SeasonalPlanner(hist, kcal)
    for line in vm.seasonal.calendar_plan(date(2026, 10, 1)):
        print("    " + line)
    import os as _os
    html_path = _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), "ledger_calendar.html")
    if _os.path.exists(html_path):
        export_calendar_html(html_path, kcal, vm.seasonal, [2026, 2027], date(2026, 9, 25))
        print("    가계부 입력 캘린더 화면 갱신: ledger_calendar.html")
    print("    ※ 2027년 설은 2월·추석은 9월 → 달력 기준으로 올해의 명절 달을 찾아 분석")
    for per in ("2026-10", "2027-01", "2027-02", "2027-04", "2027-05"):
        y, m = int(per[:4]), int(per[5:])
        txs_s = [Transaction("S1", date(y, m, 25), "(주)한빛 급여", 4_000_000, "입금"),
                 Transaction("S2", date(y, m, 1), "월세 자동이체", 900_000, "출금"),
                 Transaction("S3", date(y, m, 5), "신용대출 원리금", 700_000, "출금"),
                 Transaction("S4", date(y, m, 9), "홈플러스 결제", 1_000_000, "출금")]
        if per == "2027-05":
            txs_s.append(Transaction("S5", date(y, m, 7), "백화점 어버이날 선물", 950_000, "출금"))
        rv_s = MonthlyLedgerReview(per, txs_s, LedgerClassifier())
        rv_s.confirm_all()
        slog, _ = vm.monthly_cycle(rv_s.to_snapshot(emergency_balance=10_400_000))
        print(f"    ▶ {per} 마감:")
        for line in slog:
            if "계절성" in line or "Free_Cash" in line or line.startswith("스마트 바이"):
                print("      " + line)

    print("  [계좌별 잔여 한도 연동 — 신규 자금 매수를 한도 안에서 절세 계좌 우선 배정]")
    lm = PortfolioManager(FinancialProfile(4_000_000, 2_600_000, 12_000_000, IncomeType.REGULAR, m_multiplier=4),
                          survey, Portfolio([Holding("305080", "TIGER 미국채10년선물", IG_BOND, 300, 11_500),
                                             Holding("CMA", "CMA/파킹통장", CASH, 500_000, 1.0, settlement_days=0)]),
                          inst)
    limit_api = MockAccountLimitAPI({
        "ISA": dict(contributed_ytd=19_600_000, total_contributed=58_000_000, tax_free_used=1_400_000),
        "연금저축": dict(contributed_ytd=6_000_000),
        "IRP": dict(contributed_ytd=11_700_000, account_value=30_000_000, risky_value=20_900_000),
    })
    for line in lm.set_account_limits(limit_api):
        print("    " + line)
    llog, lprop = lm.monthly_cycle(LedgerSnapshot(4_000_000, 2_600_000, 12_000_000, total_expense=2_000_000))
    for line in llog:
        if "[계좌 한도]" in line:
            print("    " + line)
    print(lprop.render(lm.portfolio))

    _hr("거래비용·세금·정산 가드 — CostPenal 매도 순서 · 절세 계좌 · D-Day 정산")
    samples = [Holding("A1", "국내 주식형 ETF(일반)", DOM_EQ, 100, 40_000, 30_000),
               Holding("A2", "국내상장 해외 ETF(일반)", FOR_EQ, 100, 40_000, 30_000),
               Holding("A3", "국내상장 해외 ETF(ISA)", FOR_EQ, 100, 40_000, 30_000, account="ISA"),
               Holding("A4", "국내 개별 주식(일반)", DOM_EQ, 100, 40_000, 30_000, product_type="주식"),
               Holding("A5", "해외 상장 ETF(일반)", FOR_EQ, 10, 400_000, 300_000, overseas=True, settlement_days=1)]
    print("    400만 원 매도 시 예상 세금·CostPenal_i (매수가 대비 +33% 수익 가정)")
    for h in samples:
        print(f"      {h.name:<22} 세금 {won(estimate_sell_tax(h, 4_000_000)):>10}  "
              f"CostPenal {cost_penalty(h, 4_000_000):5.2f}%")
    order = sorted(samples, key=lambda h: tax_aware_sell_key(h, 4_000_000))
    print("    리밸런싱 매도 우선순위:", " → ".join(h.name for h in order))
    gm = PortfolioManager(FinancialProfile(4_000_000, 2_600_000, 12_000_000, IncomeType.REGULAR, m_multiplier=4),
                          survey, Portfolio([Holding("305080", "TIGER 미국채10년선물", IG_BOND, 100, 11_500)]), inst)
    gm.set_tax_accounts(("ISA", "연금저축", "일반"))
    o, _ = smart_buy(1_000_000, gm.portfolio, gm.targets, gm.instruments)
    print("    절세 계좌 우선 매수:", "; ".join(str(x).split("  ")[0] + " " + str(x).split(" ")[-1] for x in o[:2]))
    dd_pf = Portfolio([Holding("005930", "삼성전자", DOM_EQ, 10, 70_000, 60_000, product_type="주식"),
                       Holding("B1", "T+1 상품", FOR_EQ, 10, 100_000, 90_000, settlement_days=1),
                       Holding("B2", "T+2 상품", FOR_EQ, 100, 21_000, 18_000, settlement_days=2)])
    liq = Order("매도", "005930", "삼성전자", DOM_EQ, 20, 70_000, 0, "Trigger C", PURPOSE_LIQUIDITY, deadline_days=1)
    _, _, dd_notes, subs = pre_trade_check([liq], MockBroker(quotes={"005930": 70_000}), dd_pf)
    print("    D-Day 1일 남은 목돈 마련: 부족분 대체 매도 후보 =", [x.name for x in subs], "(T+2 상품은 제외)")

    _hr("기계적 리밸런싱 — 고정 목표 비중 유지")
    rb = PortfolioManager(FinancialProfile(4_000_000, 2_600_000, 12_000_000, IncomeType.REGULAR, m_multiplier=4),
                          survey, Portfolio([Holding("360750", "TIGER 미국S&P500", FOR_EQ, 700, 21_000, 18_000),
                                             Holding("305080", "TIGER 미국채10년선물", IG_BOND, 900, 11_500),
                                             Holding("411060", "ACE KRX금현물", COMMODITY, 160, 18_000),
                                             Holding("CMA", "CMA/파킹통장", CASH, 1_500_000, 1.0, settlement_days=0)]),
                          inst)
    print("    [주가 급등 전]", rb.daily_rebalance_check(date(2026, 12, 7))[0][1])
    rb.portfolio.find("360750").price = 27_000          # 해외주식 +28.6% 상승
    rlog, rprop = rb.daily_rebalance_check(date(2026, 12, 8))
    for line in rlog:
        print("    " + line)
    print(rb.portfolio.report(rb.targets))
    print(rprop.render(rb.portfolio))
    rb.confirm(rprop)
    rb.portfolio.find("360750").price = 29_500            # 추가 상승 (밴드 ±5%p 이내)
    print("    [6개월 뒤 정기 리밸런싱 주기 도래 — 밴드 이탈은 없음]")
    rlog, rprop = rb.daily_rebalance_check(date(2027, 6, 8))
    for line in rlog:
        print("    " + line)
    print(rprop.render(rb.portfolio))

    _hr("종목 추천 — ETF 중심, 맞는 ETF가 없을 때 단계별 대체")
    for tier in (4, 5):
        rec = ProductRecommender()
        for line in rec.report(MODEL_PORTFOLIOS[tier], per_item=1):
            print("  " + line)
        eff = rec.effective_targets(MODEL_PORTFOLIOS[tier])
        print("    실제 목표 비중:", {c: w for c, w in eff.items() if w})
    universe = [   # 사용자·증권사 제공 목록 (샘플 수치)
        Product("US01", "샘플 미국대형주 B", FOR_EQ, "개별종목", ("S&P500", "나스닥", "테마"), 250_000,
                market_cap=3e15, daily_trading_value=5e12),
    ]
    bonds = [      # 개별 채권 후보 (샘플)
        Product("KB01", "샘플 회사채 가", IG_BOND, "개별채권", (), issuer="가", rating="AA"),
        Product("KB02", "샘플 회사채 나", IG_BOND, "개별채권", (), issuer="나", rating="A+"),
        Product("KB03", "샘플 회사채 다", IG_BOND, "개별채권", (), issuer="다", rating="A"),
        Product("KB04", "샘플 회사채 라", IG_BOND, "개별채권", (), issuer="라", rating="BBB+"),
    ]
    no_corp_etf = [p for p in ETF_CATALOG if p.ticker not in ("LQD", "153130")]
    print("  [회사채·비슷한 채권 ETF가 모두 없고, 사용자가 개별 상품을 허용한 경우]")
    rec2 = ProductRecommender(etfs=no_corp_etf, allow_individual=True, stock_universe=universe, bond_universe=bonds)
    for line in rec2.report(MODEL_PORTFOLIOS[3], per_item=1):
        print("  " + line)
    print("  [같은 조건, 개별 상품 미허용]")
    r3 = ProductRecommender(etfs=no_corp_etf)
    for line in r3.report(MODEL_PORTFOLIOS[3], per_item=1)[4:6]:
        print("  " + line)
    print("    실제 목표 비중:", {c: w for c, w in r3.effective_targets(MODEL_PORTFOLIOS[3]).items() if w})
    print("  [개별 상품 허용했지만 등급 A 이상 발행사가 2곳뿐인 경우]")
    r4 = ProductRecommender(etfs=no_corp_etf, allow_individual=True, bond_universe=bonds[1:])
    for line in r4.report(MODEL_PORTFOLIOS[3], per_item=1)[4:6]:
        print("  " + line)

    _hr("STAGE 4. 정식 관리 모드 — 월간 루프")
    print(LEDGER_INPUT_GUIDE)
    mgr = PortfolioManager(profile, survey, after, inst)
    scenarios = [
        ("1개월: 평시", LedgerSnapshot(4_000_000, 2_600_000, 12_000_000)),
        ("2개월: 30일 내 이사비 2,000만 원", LedgerSnapshot(4_000_000, 2_600_000, 12_000_000,
                                                          upcoming_cf=20_000_000, dday=20)),
        ("3개월: 비상금 계좌 300만 원 출금", LedgerSnapshot(4_000_000, 2_600_000,
                                                          emergency_withdrawal=3_000_000)),
        ("4개월: 필수 지출 급증 (잔액 미입력 → 자동 계산)", LedgerSnapshot(4_000_000, 3_450_000)),
        ("5개월: 잉여율 회복", LedgerSnapshot(4_000_000, 2_650_000, 13_500_000)),
    ]
    for title, snap in scenarios:
        print(f"\n  ■ {title}")
        log, proposal = mgr.monthly_cycle(snap)
        for line in log:
            print("   - " + line)
        if proposal.orders:
            print(proposal.render(mgr.portfolio))
            res = execute_with_approval(proposal, MockBroker(), lambda p: True,
                                        datetime(2026, 9, 24, 11, 0))
            for r in res:
                print("     → " + r)
        mgr.confirm(proposal)


if __name__ == "__main__":
    main()
