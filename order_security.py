# -*- coding: utf-8 -*-
"""
주문 보안 (Order Security)

① 승인 지문     : 매매 제안 내용(종목·수량·가격·계좌·시점)의 SHA-256 지문을 승인 요청과 함께 받아,
                  서버가 가진 제안과 같을 때만 발주. 제안 유효 시간(24시간)이 지나면 만료
② 중복 방지     : 승인 요청마다 Idempotency-Key 를 받아 같은 요청은 한 번만 처리하고 같은 결과를 돌려줌
③ 주문 한도     : 1회 주문 한도·1일 누적 한도 초과 시 차단,
                  큰 주문·평소와 다른 주문은 주문 PIN 추가 인증 (5회 실패 시 10분 잠금)
④ 긴급 정지     : 켜면 모든 승인·발주 즉시 중단 (켜기는 바로, 끄기는 PIN 필요)
⑤ 권한 분리     : 증권사 인증을 조회용·주문용으로 나누고, 주문용 권한이 없으면 발주 불가
⑥ 감사 기록     : 승인·거절·차단·발주·긴급 정지를 해시 체인으로 기록 (중간 수정 시 검증 실패)

한도·PIN 등은 사용자·서비스 정책에 맞게 설정값으로 조정합니다.
"""
from __future__ import annotations

import hashlib
import hmac
import json
import os
import statistics
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from typing import Callable, Optional

import portfolio_engine as pe

PROPOSAL_TTL = timedelta(hours=24)       # 매매 제안 유효 시간
PER_ORDER_LIMIT = 10_000_000             # 1회(주문 1건) 한도
DAILY_LIMIT = 30_000_000                 # 1일 누적 주문 한도 (매수 + 매도, 현금성 이체 제외)
STEP_UP_ABS = 5_000_000                  # 이 금액 이상이면 추가 인증
STEP_UP_MULT = 3.0                       # 최근 승인 금액 중앙값의 3배 이상이면 '평소와 다른 주문'
PIN_MAX_FAIL = 5
PIN_LOCK = timedelta(minutes=10)


# ── ① 승인 지문 ───────────────────────────────────────────────────
def canonical_orders(orders: list) -> list:
    """지문 계산용 주문 표현 (순서·표기 차이 없이 같은 내용이면 같은 값)"""
    return [{"side": o.side, "ticker": o.ticker, "class": o.asset_class,
             "qty": round(float(o.quantity), 6), "price": round(float(o.price), 4),
             "day": o.day, "account": o.account or "", "purpose": o.purpose or ""}
            for o in orders]


def fingerprint(proposal_id: int, created_at: datetime, orders: list) -> str:
    body = json.dumps({"id": proposal_id, "created": created_at.isoformat(timespec="seconds"),
                       "orders": canonical_orders(orders)}, sort_keys=True, ensure_ascii=False)
    return hashlib.sha256(body.encode()).hexdigest()


def order_total(orders: list) -> float:
    return sum(o.amount for o in orders if o.asset_class != pe.CASH)


# ── ③ 추가 인증용 주문 PIN ─────────────────────────────────────────
class PinVerifier:
    """주문 PIN: scrypt 해시로만 저장, 연속 실패 시 잠금"""

    def __init__(self, pin: str, clock: Callable = datetime.now):
        if not pin or len(pin) < 6:
            raise ValueError("주문 PIN은 6자 이상이어야 합니다.")
        self.clock = clock
        self._salt = os.urandom(16)
        self._hash = self._derive(pin)
        self.failures = 0
        self.locked_until: Optional[datetime] = None

    def _derive(self, pin: str) -> bytes:
        return hashlib.scrypt(pin.encode(), salt=self._salt, n=2 ** 14, r=8, p=1, dklen=32)

    def verify(self, pin: Optional[str]) -> tuple:
        """(성공 여부, 안내)"""
        now = self.clock()
        if self.locked_until and now < self.locked_until:
            return False, f"주문 PIN {PIN_MAX_FAIL}회 실패로 {self.locked_until:%H:%M}까지 잠겼어요."
        if not pin:
            return False, "추가 인증이 필요한 주문이에요. 주문 PIN을 입력해 주세요."
        if hmac.compare_digest(self._derive(pin), self._hash):
            self.failures = 0
            return True, ""
        self.failures += 1
        if self.failures >= PIN_MAX_FAIL:
            self.failures = 0
            self.locked_until = now + PIN_LOCK
            return False, f"주문 PIN {PIN_MAX_FAIL}회 실패 → {int(PIN_LOCK.total_seconds() // 60)}분간 잠금"
        return False, f"주문 PIN이 맞지 않아요. (남은 시도 {PIN_MAX_FAIL - self.failures}회)"


# ── ⑥ 감사 기록 (해시 체인) ─────────────────────────────────────────
class AuditLog:
    """각 기록에 직전 기록의 해시를 넣어 연결 → 중간 기록을 고치면 verify() 가 실패"""

    def __init__(self, clock: Callable = datetime.now):
        self.clock = clock
        self.entries: list = []

    def append(self, event: str, **detail) -> dict:
        prev = self.entries[-1]["hash"] if self.entries else "0" * 64
        rec = {"at": self.clock().isoformat(timespec="seconds"), "event": event, "detail": detail, "prev": prev}
        rec["hash"] = hashlib.sha256(json.dumps(rec, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
        self.entries.append(rec)
        return rec

    def verify(self) -> bool:
        prev = "0" * 64
        for rec in self.entries:
            body = {k: v for k, v in rec.items() if k != "hash"}
            if rec["prev"] != prev or hashlib.sha256(
                    json.dumps(body, sort_keys=True, ensure_ascii=False).encode()).hexdigest() != rec["hash"]:
                return False
            prev = rec["hash"]
        return True


# ── ③④ 주문 한도·긴급 정지 ─────────────────────────────────────────
@dataclass
class GuardDecision:
    allowed: bool
    needs_step_up: bool = False
    reasons: list = field(default_factory=list)


class OrderGuard:
    def __init__(self, per_order: float = PER_ORDER_LIMIT, daily: float = DAILY_LIMIT,
                 step_up_abs: float = STEP_UP_ABS, step_up_mult: float = STEP_UP_MULT,
                 clock: Callable = datetime.now):
        self.per_order, self.daily = per_order, daily
        self.step_up_abs, self.step_up_mult = step_up_abs, step_up_mult
        self.clock = clock
        self.halted = False
        self.halt_reason = ""
        self.history: list = []          # [(시각, 승인 금액)]

    def daily_used(self) -> float:
        today = self.clock().date()
        return sum(a for t, a in self.history if t.date() == today)

    def usual_amount(self) -> Optional[float]:
        recent = [a for _, a in self.history[-6:] if a > 0]
        return statistics.median(recent) if len(recent) >= 3 else None

    def check(self, orders: list) -> GuardDecision:
        if self.halted:
            return GuardDecision(False, reasons=[f"긴급 정지 중: {self.halt_reason or '사유 미기재'}"])
        reasons = []
        for o in orders:
            if o.asset_class != pe.CASH and o.amount > self.per_order:
                reasons.append(f"{o.side} {o.name} {pe.won(o.amount)} > 1회 주문 한도 {pe.won(self.per_order)}")
        total = order_total(orders)
        used = self.daily_used()
        if used + total > self.daily:
            reasons.append(f"오늘 누적 {pe.won(used)} + 이번 {pe.won(total)} > 1일 한도 {pe.won(self.daily)}")
        if reasons:
            return GuardDecision(False, reasons=reasons)
        step, why = False, []
        if total >= self.step_up_abs:
            step, why = True, [f"주문 합계 {pe.won(total)} ≥ 추가 인증 기준 {pe.won(self.step_up_abs)}"]
        usual = self.usual_amount()
        if usual and total >= usual * self.step_up_mult:
            step = True
            why.append(f"최근 승인 금액(중앙값 {pe.won(usual)})의 {self.step_up_mult:.0f}배 이상")
        return GuardDecision(True, step, why)

    def record(self, orders: list) -> None:
        self.history.append((self.clock(), order_total(orders)))


# ── ⑤ 증권사 권한 분리 ─────────────────────────────────────────────
class ScopedBroker(pe.BrokerAPI):
    """
    증권사 연결을 조회용·주문용 권한으로 분리
    - 현재가·예수금 조회: 조회용 토큰
    - 발주: 주문용 토큰이 있을 때만 (없으면 PermissionError)
    토큰은 환경변수·KMS 에서만 읽고, 화면(브라우저)으로는 절대 보내지 않음
    """

    def __init__(self, broker: pe.BrokerAPI, read_token: Optional[str], trade_token: Optional[str]):
        self._broker = broker
        self._read = read_token
        self._trade = trade_token

    @property
    def can_trade(self) -> bool:
        return bool(self._trade)

    def get_quote(self, ticker):
        if not self._read:
            raise PermissionError("조회용 증권사 권한이 없습니다.")
        return self._broker.get_quote(ticker)

    def get_deposit(self):
        if not self._read:
            raise PermissionError("조회용 증권사 권한이 없습니다.")
        return self._broker.get_deposit()

    def place_order(self, order):
        if not self._trade:
            raise PermissionError("주문용 증권사 권한이 없어 발주할 수 없습니다.")
        return self._broker.place_order(order)
