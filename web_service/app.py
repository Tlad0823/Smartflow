# -*- coding: utf-8 -*-
"""
가계부 연동 자산배분 웹 서비스 (백엔드)

- portfolio_engine.py 의 계산 로직을 그대로 쓰고, 화면과는 JSON API로만 주고받습니다.
- 화면(static/index.html)은 한 페이지 안에 홈·가계부(캘린더)·포트폴리오·매매 제안 탭을 둡니다.

실행:  pip install -r requirements.txt  →  python app.py  →  http://127.0.0.1:5000
공휴일 API: 환경변수 HOLIDAY_API_KEY 에 공공데이터포털 인증키를 넣으면 특일 정보 API를 사용,
           없으면 내장 예비 데이터를 사용합니다.

주문 보안: order_security.py — 승인 지문·중복 방지·주문 한도/추가 인증·긴급 정지·권한 분리·감사 기록
  ORDER_PIN(주문 PIN), BROKER_READ_TOKEN / BROKER_TRADE_TOKEN(증권사 조회·주문 권한)은 환경변수로 설정

저장: storage.py — 상태가 바뀔 때마다 SQLite(PORTFOLIO_DB, 기본 data/portfolio.db)에 저장, 켤 때 불러옴

※ 1인용으로 동작합니다. 여러 사용자에게 제공하려면 로그인·사용자별 데이터 분리·HTTPS·CSRF 방지가
  필요합니다 (README 참고).
"""
from __future__ import annotations

import os
import threading
from datetime import date, datetime, timedelta
from typing import Optional

from flask import Flask, abort, jsonify, request, send_from_directory

import portfolio_engine as pe
# 모의 날짜로 실행: PORTFOLIO_TODAY=2026-10-02 (또는 2026-10-02T11:00) → 그 시각부터 시간이 흐름
if os.environ.get("PORTFOLIO_TODAY"):
    _v = os.environ["PORTFOLIO_TODAY"]
    pe.set_clock(pe.OffsetClock(datetime.fromisoformat(_v) if "T" in _v else date.fromisoformat(_v)))

from storage import Store, StorageError
from order_security import (PROPOSAL_TTL, AuditLog, OrderGuard, PinVerifier, ScopedBroker,
                            fingerprint, order_total)

app = Flask(__name__, static_folder="static", static_url_path="/static")
_lock = threading.Lock()


# ════════════════════════════════════════════════════════════════════
# 서비스 상태 (1명 사용자, SQLite 저장: storage.py)
# ════════════════════════════════════════════════════════════════════
class ServiceState:
    # 저장하지 않고 켤 때마다 환경 변수로 다시 만드는 항목 (토큰·PIN)
    RUNTIME = ("broker", "pin")

    def __init__(self, today: date):
        self.today = today
        self.calendar = pe.KoreanCalendar(None)
        self.profile = pe.FinancialProfile(4_000_000, 2_600_000, 12_000_000, pe.IncomeType.REGULAR,
                                           monthly_debt_payment=700_000, m_multiplier=4)
        self.survey = pe.SurveyAnswers(50, 66, 66, 75, 66, goals=pe.LifeGoals(1992, 60))
        portfolio = pe.Portfolio([
            pe.Holding("360750", "TIGER 미국S&P500", pe.FOR_EQ, 700, 21_000, 18_000, account="ISA"),
            pe.Holding("133690", "TIGER 미국나스닥100", pe.FOR_EQ, 20, 112_500, 118_000),
            pe.Holding("305080", "TIGER 미국채10년선물", pe.IG_BOND, 900, 11_500, 11_000, maturity_months=120),
            pe.Holding("411060", "ACE KRX금현물", pe.COMMODITY, 160, 18_000, 17_000),
            pe.Holding("CMA", "CMA/파킹통장", pe.CASH, 1_500_000, 1.0, settlement_days=0),
        ])
        self.manager = pe.PortfolioManager(self.profile, self.survey, portfolio, pe.demo_instruments())
        self.manager.last_emergency_balance = 10_400_000
        history = [("2025-10", 3_800_000), ("2025-11", 2_600_000), ("2025-12", 2_950_000),
                   ("2026-01", 2_650_000), ("2026-02", 3_300_000), ("2026-03", 2_600_000),
                   ("2026-04", 2_650_000), ("2026-05", 3_600_000), ("2026-06", 2_600_000),
                   ("2026-07", 2_700_000), ("2026-08", 2_650_000)]
        self.manager.seasonal = pe.SeasonalPlanner(history, self.calendar)
        self.events: dict = {}                      # id → CalendarEvent (사용자 지출)
        self.entries: dict = {}                     # id → 일일 가계부 기록 {tx, override}
        self.classifier = pe.LedgerClassifier()     # 가맹점 단위 자동 분류 (사용자 규칙 학습)
        self.ledgers: dict = {}                     # YYYY-MM → 입력값
        self.proposals: dict = {}                   # id → 제안·상태·지문·생성 시각
        self.last_id = 0                            # 일정·기록·제안 번호
        # ── 주문 보안 ──
        self.guard = OrderGuard(clock=pe.clock_now)
        self.audit = AuditLog(clock=pe.clock_now)
        self.idempotency: dict = {}                 # Idempotency-Key → (상태 코드, 응답)
        self.attach_runtime()
        self.add_event(date(2026, 10, 3), "추석 연휴 가족 여행 잔금", 600_000, False)
        for d, k, a, desc in [(1, "출금", 900_000, "월세 자동이체"), (5, "출금", 700_000, "신용대출 원리금"),
                              (9, "출금", 86_000, "이마트 장보기"), (12, "출금", 18_500, "배달의민족"),
                              (15, "입금", 120_000, "중고거래 판매"), (20, "출금", 150_000, "OO생명 보험료"),
                              (23, "출금", 45_000, "CGV 영화")]:
            self.add_entry(date(today.year, today.month, d), k, a, desc)
        self.add_event(date(2026, 11, 20), "전세 보증금 증액", 15_000_000, True)

    def attach_runtime(self, pin_state: Optional[dict] = None) -> None:
        """환경 변수에서 비밀값을 채우고 엔진 전역 달력을 연결 (처음 만들 때와 DB에서 불러올 때 모두)"""
        key = os.environ.get("HOLIDAY_API_KEY")
        self.calendar.provider = pe.DataGoKrHolidayAPI(key) if key else None
        # 한국(공휴일 API·KRX 규정)·미국(NYSE 규칙) 증시 달력 → 엔진의 T+N 정산일·매도 후보·매수 집행일 계산에 사용
        closures = os.path.join(os.path.dirname(os.path.abspath(__file__)), "market_closures.json")
        pe.set_market_calendar(pe.MarketCalendar.with_closure_file(self.calendar, closures))
        self.pin = PinVerifier(os.environ.get("ORDER_PIN", "135790"), clock=pe.clock_now)      # 데모 PIN — 운영 시 반드시 변경
        for k, v in (pin_state or {}).items():      # 연속 실패·잠금 상태는 재시작해도 유지
            setattr(self.pin, k, v)
        self.broker = ScopedBroker(pe.MockBroker(), os.environ.get("BROKER_READ_TOKEN", "demo-read"),
                                   os.environ.get("BROKER_TRADE_TOKEN", "demo-trade"))

    def next_id(self) -> int:
        self.last_id += 1
        return self.last_id

    def persistable(self) -> dict:
        state = {k: v for k, v in self.__dict__.items() if k not in self.RUNTIME}
        state["_pin_state"] = {"failures": self.pin.failures, "locked_until": self.pin.locked_until}
        return state

    @classmethod
    def restore(cls, state: dict) -> "ServiceState":
        state = dict(state)
        pin_state = state.pop("_pin_state", None)
        obj = cls.__new__(cls)
        obj.__dict__.update(state)
        obj.attach_runtime(pin_state)
        return obj

    def add_event(self, day: date, name: str, amount: float, big: bool) -> int:
        ev = self.calendar.add_user_event(day, name, amount, big)
        eid = self.next_id()
        self.events[eid] = ev
        return eid

    def add_entry(self, day: date, kind: str, amount: float, desc: str, override: str = "auto") -> int:
        eid = self.next_id()
        self.entries[eid] = {"tx": pe.Transaction(f"E{eid}", day, desc, amount, kind), "override": override}
        return eid

    def delete_event(self, eid: int) -> None:
        ev = self.events.pop(eid)
        self.calendar.user_events.remove(ev)


# ── 시연 모드: PORTFOLIO_DEMO=1 (demo.py 가 켬) ──
#   다른 사람에게 링크로 보여 줄 때: 저장된 내 데이터를 절대 불러오거나 덮어쓰지 않고, 데모 데이터로 메모리에서만 동작
DEMO = os.environ.get("PORTFOLIO_DEMO", "").strip() == "1"

# ── 저장소: PORTFOLIO_DB (기본 data/portfolio.db, "off" 면 메모리만) ──
_DB = os.environ.get("PORTFOLIO_DB", os.path.join(os.path.dirname(os.path.abspath(__file__)), "data", "portfolio.db"))
STORE = None if DEMO or _DB.strip().lower() in ("", "off", "none", "memory") else Store(_DB)
STORAGE = {"path": None if STORE is None else os.path.abspath(_DB), "lastSaved": None, "error": None,
           "loadedFrom": None}


def _boot() -> "ServiceState":
    """저장된 상태가 있으면 불러오고, 없으면 새로 시작 (데모 데이터)"""
    if STORE is not None:
        try:
            data = STORE.load()
        except StorageError as e:
            # 기존 데이터를 덮어쓰지 않도록 여기서 멈춤
            raise SystemExit(f"[저장소] {e}\n  DB 파일: {STORAGE['path']}\n"
                             "  기존 데이터를 보존하려고 서버를 시작하지 않았어요. 파일을 다른 곳으로 옮기거나 "
                             "PORTFOLIO_DB 로 새 경로를 지정하면 새로 시작합니다.")
        if data is not None:
            STORAGE["loadedFrom"] = STORE.history(1)[0]
            return ServiceState.restore(data)
    return ServiceState(pe.clock_today())


STATE = _boot()


def save_state(reason: str) -> None:
    """현재 상태를 DB에 저장 (호출하는 쪽에서 _lock 을 잡고 있어야 함)"""
    if STORE is None:
        return
    try:
        STORE.save(STATE.persistable(), reason, pe.clock_now())
        STORAGE["lastSaved"], STORAGE["error"] = pe.clock_now().isoformat(timespec="seconds"), None
    except Exception as e:                          # 저장 실패는 화면에 알리되 요청 자체는 끝까지 처리
        STORAGE["error"] = f"{type(e).__name__}: {e}"
        app.logger.error("상태 저장 실패: %s", e)


@app.after_request
def _persist_after_change(resp):
    """상태를 바꾸는 요청(POST·PUT·DELETE)이 끝나면 저장"""
    if request.method in ("POST", "PUT", "DELETE") and resp.status_code < 500:
        with _lock:
            save_state(f"{request.method} {request.path}")
    return resp


# ════════════════════════════════════════════════════════════════════
# 직렬화 도우미
# ════════════════════════════════════════════════════════════════════
def _period(year: int, month: int) -> str:
    return f"{year}-{month:02d}"


def _next_month(year: int, month: int) -> tuple:
    return (year + 1, 1) if month == 12 else (year, month + 1)


def _event_json(ev: pe.CalendarEvent, eid=None) -> dict:
    out = {"id": eid, "date": ev.day.isoformat(), "name": ev.name, "kind": ev.kind,
           "amount": ev.amount, "big": ev.big}
    today = pe.clock_today()
    if ev.big and ev.day >= today:              # 목돈 지출: 달력 D-Day와 남은 영업일을 함께 표시
        out.update(dday=(ev.day - today).days, bdays=pe.market_calendar().business_days_until(today, ev.day))
    return out


def _order_json(o: pe.Order, late: tuple = ()) -> dict:
    due = getattr(o.deadline_days, "due", None)
    return {"dueDate": due.isoformat() if due else None, "late": any(o is x for x in late),
            "side": o.side, "name": o.name, "assetClass": o.asset_class, "quantity": o.quantity,
            "price": o.price, "amount": round(o.amount), "day": o.day, "reason": o.reason,
            "execDate": o.exec_date.isoformat() if getattr(o, "exec_date", None) else None,
            "cashDate": o.cash_date.isoformat() if getattr(o, "cash_date", None) else None,
            "purpose": o.purpose, "account": o.account}


def _num(body: dict, key: str, required: bool = False):
    v = body.get(key)
    if v in (None, ""):
        if required:
            abort(400, description=f"{key} 값이 필요합니다.")
        return None
    try:
        v = float(v)
    except (TypeError, ValueError):
        abort(400, description=f"{key} 는 숫자여야 합니다.")
    if v < 0:
        abort(400, description=f"{key} 는 0 이상이어야 합니다.")
    return v


def _ledger_preview(period: str, L: dict) -> dict:
    snap = pe.LedgerSnapshot(L.get("monthly_income") or 0, L.get("essential_expense") or 0,
                             L.get("emergency_balance"), total_expense=L.get("total_expense") or 0, period=period,
                             irregular_income=L.get("irregular_income") or 0,
                             irregular_taxable=L.get("irregular_taxable") or 0)
    free = snap.free_cash
    invest, reserve, note = STATE.manager.seasonal.plan(period, free)
    plan = STATE.manager.plan_irregular(snap, reserve)
    queued = STATE.manager.irregular_dca_queue[0] if STATE.manager.irregular_dca_queue else 0.0
    return {"freeCash": round(free), "reserve": round(reserve),
            "invest": round(max(0.0, invest) + plan.invest_now + queued),
            "note": note, "buffer": round(snap.buffer, 1),
            "irregular": {"amount": round(plan.amount), "emergency": round(plan.to_emergency),
                          "upcoming": round(plan.to_upcoming), "seasonal": round(plan.to_seasonal),
                          "tax": round(plan.to_tax), "investNow": round(plan.invest_now),
                          "investLater": [round(x) for x in plan.invest_later], "queued": round(queued),
                          "lines": plan.lines()}}


# ════════════════════════════════════════════════════════════════════
# API
# ════════════════════════════════════════════════════════════════════
@app.errorhandler(400)
@app.errorhandler(404)
def _err(e):
    return jsonify(error=getattr(e, "description", str(e))), e.code


@app.get("/")
def index():
    return send_from_directory(app.static_folder, "index.html")


@app.get("/api/summary")
def summary():
    m = STATE.manager
    with _lock:
        ratios = m.portfolio.current_ratios()
        targets = m.targets
        reserve_need = m.c_reserve(STATE.profile.essential_expense)
        y, mo = _next_month(STATE.today.year, STATE.today.month)
        extra, why = m.seasonal.expected_extra(y, mo)
        pending = sum(1 for p in STATE.proposals.values() if p["status"] == "승인 대기")
        return jsonify(
            today=STATE.today.isoformat(),
            tier={"level": m.current_tier, "name": pe.TIER_NAMES[m.current_tier],
                  "score": round(m.risk.final, 1)},
            emergency={"balance": round(m.last_emergency_balance or 0), "required": round(reserve_need)},
            triggers=[t.value for t in (m.prev_triggers | getattr(m, "event_triggers", set()))],
            portfolio={"total": round(m.portfolio.total()),
                       "classes": [{"name": c, "current": round(ratios[c], 1), "target": targets.get(c, 0),
                                    "gap": round(ratios[c] - targets.get(c, 0), 1),
                                    "value": round(m.portfolio.class_values()[c])}
                                   for c in pe.ASSET_CLASSES if ratios[c] or targets.get(c)]},
            nextMonth={"period": _period(y, mo), "extra": round(extra), "why": why},
            holdings=_holdings_json(m.portfolio),
            reserves={"tax": round(m.tax_reserve), "expense": round(getattr(m, "expense_reserve", 0.0)),
                      "seasonal": round(sum(m.seasonal_reserves.values())),
                      "irregularQueue": [round(x) for x in m.irregular_dca_queue]},
            pendingProposals=pending,
            band=pe.REBALANCE_BAND,
        )


def _holdings_json(portfolio: pe.Portfolio) -> list:
    """자산군별 보유 종목: 수량·평균 매수가·현재가·평가액·평가손익"""
    groups = []
    for c in pe.ASSET_CLASSES:
        items = [h for h in portfolio.holdings if h.asset_class == c and h.quantity > 0]
        if not items:
            continue
        rows = []
        for h in sorted(items, key=lambda h: -h.value):
            cash = h.asset_class == pe.CASH
            rows.append({"ticker": h.ticker, "name": h.name, "account": h.account, "cash": cash,
                         "quantity": h.quantity, "fractional": h.fractional and not cash,
                         "avgPrice": round(h.avg_price, 2), "price": round(h.price, 2), "value": round(h.value),
                         "profit": 0 if cash else round((h.price - h.avg_price) * h.quantity),
                         "profitPct": 0.0 if cash else round(h.profit_pct, 2), "locked": h.locked})
        groups.append({"assetClass": c, "value": round(sum(r["value"] for r in rows)), "items": rows})
    return groups


@app.get("/api/calendar")
def calendar():
    try:
        year, month = int(request.args["year"]), int(request.args["month"])
        assert 1 <= month <= 12 and 2000 <= year <= 2100
    except (KeyError, ValueError, AssertionError):
        abort(400, description="year, month 가 올바르지 않습니다.")
    with _lock:
        cal = STATE.calendar
        ids = {id(ev): eid for eid, ev in STATE.events.items()}
        events = [_event_json(e, ids.get(id(e))) for e in cal.events_in_month(year, month)]
        ny, nm = _next_month(year, month)
        extra, why = STATE.manager.seasonal.expected_extra(ny, nm)
        period = _period(year, month)
        L = STATE.ledgers.get(period, {})
        daily = _entries_payload(year, month)
        return jsonify(year=year, month=month, events=events, entries=daily["entries"],
                       entrySummary=daily["summary"],
                       source=cal.sources.get(year, ""),
                       nextMonth={"period": _period(ny, nm), "extra": round(extra), "why": why},
                       ledger=L, preview=_ledger_preview(period, L) if L else None,
                       maxHold=pe.SEASONAL_MAX_HOLD, taxRatio=pe.IRREGULAR_TAX_RATIO,
                       market=pe.market_calendar().month_events(year, month),
                       marketSource=pe.market_calendar().source(year))


@app.post("/api/events")
def add_event():
    body = request.get_json(silent=True) or {}
    name = str(body.get("name", "")).strip()
    if not name or len(name) > 40:
        abort(400, description="지출 이름을 1~40자로 입력해 주세요.")
    try:
        day = date.fromisoformat(body.get("date", ""))
    except ValueError:
        abort(400, description="날짜 형식이 올바르지 않습니다.")
    amount = _num(body, "amount", required=True)
    with _lock:
        eid = STATE.add_event(day, name, amount, bool(body.get("big")))
        return jsonify(_event_json(STATE.events[eid], eid)), 201


@app.delete("/api/events/<int:eid>")
def delete_event(eid: int):
    with _lock:
        if eid not in STATE.events:
            abort(404, description="해당 지출 일정이 없습니다.")
        STATE.delete_event(eid)
        return ("", 204)


@app.put("/api/ledger/<period>")
def save_ledger(period: str):
    try:
        y, m = int(period[:4]), int(period[5:7])
        assert len(period) == 7 and period[4] == "-" and 1 <= m <= 12
    except (ValueError, AssertionError):
        abort(400, description="기간은 YYYY-MM 형식이어야 합니다.")
    body = request.get_json(silent=True) or {}
    L = {k: _num(body, k) for k in ("monthly_income", "total_expense", "essential_expense",
                                    "emergency_deposit", "emergency_withdrawal", "emergency_balance",
                                    "irregular_income", "irregular_taxable")}
    if (L["irregular_taxable"] or 0) > (L["irregular_income"] or 0):
        abort(400, description="사업·용역 소득은 비정기 수입보다 클 수 없어요.")
    if L["monthly_income"] is None or L["essential_expense"] is None:
        abort(400, description="월 확정 수입과 필수 고정 지출은 꼭 입력해 주세요.")
    with _lock:
        STATE.ledgers[period] = L
        return jsonify(ledger=L, preview=_ledger_preview(period, L))


@app.post("/api/ledger/<period>/preview")
def preview_ledger(period: str):
    """저장하지 않고 순잉여금·계절 대비·비정기 수입 배분만 계산"""
    body = request.get_json(silent=True) or {}
    L = {k: _num(body, k) for k in ("monthly_income", "total_expense", "essential_expense", "emergency_balance",
                                    "irregular_income", "irregular_taxable")}
    with _lock:
        return jsonify(preview=_ledger_preview(period, L))


@app.post("/api/ledger/<period>/close")
def close_month(period: str):
    """월 마감: 가계부 → 트리거 판단·스마트 바이·기계적 리밸런싱 → 매매 제안 생성"""
    with _lock:
        L = STATE.ledgers.get(period)
        if not L:
            abort(400, description="먼저 이번 달 가계부를 저장해 주세요.")
        y, m = int(period[:4]), int(period[5:7])
        ny, nm = _next_month(y, m)
        close_day = pe.clock_today()      # 판단일·매도 주문일 (월말 전에 미리 마감해도 오늘 기준)
        cf, dday, bdays, due, _ = pe.upcoming_big_expenses(STATE.calendar.big_events(), close_day)
        daily = _entries_payload(y, m)["summary"]
        irr = L.get("irregular_income")
        irr_tax = L.get("irregular_taxable")
        if irr is None:
            irr, irr_tax = daily["irregularIncome"], daily["irregularTaxable"]
        snap = pe.LedgerSnapshot(
            L["monthly_income"], L["essential_expense"], L.get("emergency_balance"),
            L.get("emergency_deposit") or 0, L.get("emergency_withdrawal") or 0,
            upcoming_cf=cf, dday=dday, bdays=bdays, due_date=due, as_of=close_day,
            period=period, total_expense=L.get("total_expense") or 0,
            irregular_income=irr or 0, irregular_taxable=irr_tax or 0)
        log, proposal = STATE.manager.monthly_cycle(snap, today=close_day)
        pe.schedule_orders(proposal.orders, STATE.manager.portfolio, close_day, STATE.manager.instruments)
        pid = STATE.next_id()
        created = pe.clock_now().replace(microsecond=0)
        fp = fingerprint(pid, created, proposal.orders)
        STATE.proposals[pid] = {"proposal": proposal, "status": "승인 대기" if proposal.orders else "주문 없음",
                                "period": period, "log": log, "created": created, "fingerprint": fp,
                                "origin": "월 마감"}
        STATE.audit.append("제안 생성", id=pid, period=period, orders=len(proposal.orders),
                           total=round(order_total(proposal.orders)), fingerprint=fp[:16])
        return jsonify(id=pid, period=period, log=log, orders=[_order_json(o) for o in proposal.orders],
                       extra=proposal.extra, fingerprint=fp)


def _refresh_expiry(p: dict) -> None:
    if p["status"] == "승인 대기" and pe.clock_now() - p["created"] > PROPOSAL_TTL:
        p["status"] = "만료"
        STATE.audit.append("제안 만료", fingerprint=p["fingerprint"][:16])


def _reschedule(p: dict) -> list:
    """
    승인 대기 제안의 집행일·대금 입금일을 지금 시각 기준으로 다시 계산
    (주말·휴장일·장 마감을 지나면 날짜가 밀림) → 목돈 지출일을 넘기게 된 매도 목록
    """
    orders = p["proposal"].orders
    pe.schedule_orders(orders, STATE.manager.portfolio, pe.clock_now(), STATE.manager.instruments)
    return pe.late_sells(orders)


def _late_json(late: list) -> list:
    return [{"name": o.name, "amount": round(o.amount), "cashDate": o.cash_date.isoformat(),
             "dueDate": o.deadline_days.due.isoformat()} for o in late]


@app.get("/api/proposals")
def proposals():
    with _lock:
        out = []
        for pid, p in sorted(STATE.proposals.items(), reverse=True):
            _refresh_expiry(p)
            late = _reschedule(p) if p["status"] == "승인 대기" else []
            orders = p["proposal"].orders
            d = STATE.guard.check(orders) if p["status"] == "승인 대기" else None
            out.append({"id": pid, "period": p["period"], "status": p["status"], "origin": p.get("origin", "월 마감"),
                        "orders": [_order_json(o, tuple(late)) for o in orders], "log": p["log"],
                        "lateSells": _late_json(late),
                        "fingerprint": p["fingerprint"], "total": round(order_total(orders)),
                        "createdAt": p["created"].isoformat(),
                        "expiresAt": (p["created"] + PROPOSAL_TTL).isoformat(),
                        "guard": None if d is None else {"allowed": d.allowed, "stepUp": d.needs_step_up,
                                                         "reasons": d.reasons},
                        "results": p.get("results", [])})
        return jsonify(out)


def _idempotent(key: str, status: int, body: dict):
    STATE.idempotency[key] = (status, body)
    return jsonify(body), status


@app.post("/api/proposals/<int:pid>/<action>")
def decide(pid: int, action: str):
    """
    1-Click 승인·거절 (주문 보안 적용)
      헤더 Idempotency-Key 필수 — 같은 키로 다시 요청하면 처음 결과를 그대로 돌려줌 (중복 발주 방지)
      본문 {fingerprint, pin?} — 지문이 서버의 제안과 같아야 하고, 큰 주문은 주문 PIN 필요
    """
    key = request.headers.get("Idempotency-Key", "")
    if not (8 <= len(key) <= 100):
        abort(400, description="Idempotency-Key 헤더가 필요합니다.")
    if action not in ("approve", "reject"):
        abort(400, description="approve 또는 reject 만 가능합니다.")
    body = request.get_json(silent=True) or {}
    with _lock:
        if key in STATE.idempotency:                                  # ② 중복 요청
            status, resp = STATE.idempotency[key]
            return jsonify({**resp, "replayed": True}), status
        p = STATE.proposals.get(pid)
        if not p:
            abort(404, description="해당 매매 제안이 없습니다.")
        _refresh_expiry(p)
        if p["status"] != "승인 대기":
            return _idempotent(key, 409, {"error": f"이미 처리된 제안입니다 ({p['status']})."})
        orders = p["proposal"].orders

        # ① 승인 지문: 화면이 본 제안 = 서버가 가진 제안 = 생성 당시 제안
        current = fingerprint(pid, p["created"], orders)
        if body.get("fingerprint") != p["fingerprint"] or current != p["fingerprint"]:
            STATE.audit.append("지문 불일치 차단", id=pid, action=action)
            return _idempotent(key, 409, {"error": "제안 내용이 확인한 내용과 달라요. 목록을 새로 고친 뒤 다시 확인해 주세요."})

        if action == "reject":
            p["status"] = "거절"
            STATE.audit.append("거절", id=pid, fingerprint=p["fingerprint"][:16])
            return _idempotent(key, 200, {"id": pid, "status": p["status"]})

        # ② 승인 시점 재계산: 제안 이후 시간이 지나 목돈 지출일 안에 대금이 못 들어오게 된 매도는 확인받기
        late = _reschedule(p)
        if late:
            names = [o.name for o in late]
            if not body.get("acceptLate"):
                STATE.audit.append("지출일 초과 매도 확인 요청", id=pid, orders=names)
                # 사용자가 확인한 뒤 다시 보낼 수 있어야 하므로 멱등 결과로 저장하지 않음
                return jsonify(error="승인 시점 기준으로 다시 계산하니 목돈 지출일까지 매도 대금이 들어오지 않는 주문이 있어요.",
                               needsAck=True, lateSells=_late_json(late)), 409
            STATE.audit.append("지출일 초과 매도 확인 후 승인", id=pid, orders=names)

        # ③④ 한도·긴급 정지·추가 인증
        d = STATE.guard.check(orders)
        if not d.allowed:
            STATE.audit.append("한도·정지 차단", id=pid, reasons=d.reasons)
            return _idempotent(key, 403, {"error": "주문이 차단됐어요.", "reasons": d.reasons})
        if d.needs_step_up:
            ok, msg = STATE.pin.verify(body.get("pin"))
            if not ok:
                STATE.audit.append("추가 인증 실패", id=pid, reason=msg)
                # PIN 오류는 다시 시도할 수 있어야 하므로 멱등 결과로 저장하지 않음
                return jsonify(error=msg, stepUp=True, reasons=d.reasons), 401
            STATE.audit.append("추가 인증 성공", id=pid)

        # ⑤ 주문용 권한 확인 (장 시간 밖이라 예약되는 주문도 미리 확인)
        if any(o.asset_class != pe.CASH for o in orders) and not STATE.broker.can_trade:
            STATE.audit.append("권한 없음 차단", id=pid)
            return _idempotent(key, 403, {"error": "주문용 증권사 권한이 연결되지 않아 발주할 수 없어요."})
        try:
            results = pe.execute_with_approval(p["proposal"], STATE.broker, lambda _: True, pe.clock_now(),
                                               portfolio=STATE.manager.portfolio)
        except PermissionError as e:
            STATE.audit.append("권한 없음 차단", id=pid, reason=str(e))
            return _idempotent(key, 403, {"error": str(e)})
        STATE.manager.confirm(p["proposal"])       # 데모: 체결된 것으로 가정해 반영
        STATE.guard.record(orders)
        p["status"], p["results"] = "승인 완료", results
        STATE.audit.append("승인·발주", id=pid, fingerprint=p["fingerprint"][:16],
                           total=round(order_total(orders)), orders=len(orders))
        return _idempotent(key, 200, {"id": pid, "status": p["status"], "results": results})


@app.get("/api/demo")
def demo_status():
    return jsonify(demo=DEMO)


@app.post("/api/demo/reset")
def demo_reset():
    """시연 중 데이터를 처음 데모 상태로 되돌리기 (발표자용 — 주문 PIN 필요)"""
    global STATE
    if not DEMO:
        abort(404)
    body = request.get_json(silent=True) or {}
    with _lock:
        ok, msg = STATE.pin.verify(body.get("pin"))
        if not ok:
            return jsonify(error=msg), 401
        STATE = ServiceState(pe.clock_today())
        MONITOR.update(last=None, history=[])      # 이전 방문자들의 스캔 기록도 지움
    return jsonify(ok=True)


@app.get("/api/storage")
def storage_status():
    """저장소 상태: DB 경로, 마지막 저장 시각, 오류, 최근 스냅숏"""
    with _lock:
        return jsonify(dict(STORAGE, history=STORE.history(5) if STORE else []))


@app.get("/api/security")
def security():
    with _lock:
        g = STATE.guard
        return jsonify(halted=g.halted, haltReason=g.halt_reason,
                       limits={"perOrder": g.per_order, "daily": g.daily, "stepUp": g.step_up_abs,
                               "stepUpMult": g.step_up_mult, "proposalTtlHours": PROPOSAL_TTL.total_seconds() / 3600},
                       dailyUsed=round(g.daily_used()), canTrade=STATE.broker.can_trade,
                       auditValid=STATE.audit.verify(),
                       audit=[{"at": e["at"], "event": e["event"], "detail": e["detail"]}
                              for e in STATE.audit.entries[-15:]][::-1])


@app.post("/api/kill-switch")
def kill_switch():
    """긴급 정지: 켜기는 즉시(사유 기록), 끄기는 주문 PIN 필요"""
    body = request.get_json(silent=True) or {}
    on = bool(body.get("on"))
    with _lock:
        g = STATE.guard
        if on:
            g.halted, g.halt_reason = True, str(body.get("reason") or "사용자 긴급 정지")[:100]
            STATE.audit.append("긴급 정지 켬", reason=g.halt_reason)
        else:
            ok, msg = STATE.pin.verify(body.get("pin"))
            if not ok:
                STATE.audit.append("긴급 정지 해제 실패", reason=msg)
                return jsonify(error=msg), 401
            g.halted, g.halt_reason = False, ""
            STATE.audit.append("긴급 정지 해제")
        return jsonify(halted=g.halted, haltReason=g.halt_reason)



# ════════════════════════════════════════════════════════════════════
# 투자 성향 진단 (STAGE 1 재무 체력 + STAGE 2 설문 → 등급)
# ════════════════════════════════════════════════════════════════════
QUESTIONS = [
    {"key": "q1_1", "group": "Tol", "weight": 0.40, "title": "투자한 돈이 얼마까지 줄어들어도 견딜 수 있나요?",
     "options": [(0, "원금은 절대 잃고 싶지 않아요"), (25, "-5% 정도까지"), (50, "-15% 정도까지"),
                 (75, "-30% 정도까지"), (100, "-30%보다 더 떨어져도 괜찮아요")]},
    {"key": "q1_2", "group": "Tol", "weight": 0.35, "title": "시장이 크게 떨어져 내 자산이 20% 줄었다면?",
     "options": [(0, "모두 팔아서 손실을 멈춘다"), (33, "일부를 판다"), (66, "그대로 두고 지켜본다"),
                 (100, "싸게 살 기회로 보고 더 산다")]},
    {"key": "q1_3", "group": "Tol", "weight": 0.25, "title": "원하는 수익과 위험의 수준은?",
     "options": [(0, "원금 보장이 가장 중요해요"), (33, "예적금보다 1~2% 높은 정도"),
                 (66, "물가상승률을 넉넉히 넘는 정도"), (100, "시장 평균 이상의 높은 수익")]},
    {"key": "q2_1", "group": "Horizon", "weight": 0.60, "title": "이 돈을 얼마나 오래 투자할 수 있나요?",
     "options": [(0, "6개월 미만"), (25, "6개월 ~ 1년"), (50, "1년 ~ 3년"), (75, "3년 ~ 5년"), (100, "5년 이상")]},
    {"key": "q2_2", "group": "Horizon", "weight": 0.40, "title": "이 돈은 어떤 성격의 돈인가요?",
     "options": [(0, "1년 안에 꼭 써야 하는 돈"), (33, "1~3년 안에 꺼내 쓸 수도 있는 돈"),
                 (66, "상황에 따라 꺼낼 수 있는 여유 자금"), (100, "노후 등 장기 목적 자금")]},
]


def _build_onboarding(body: dict) -> tuple:
    """입력 검증 → (FinancialProfile, SurveyAnswers)"""
    try:
        itype = pe.IncomeType[body.get("income_type", "")]
    except KeyError:
        abort(400, description="소득 유형을 선택해 주세요.")
    vals = {k: _num(body, k, required=k in ("monthly_fixed_income", "essential_expense", "cash_current"))
            for k in ("monthly_fixed_income", "essential_expense", "cash_current", "monthly_debt_payment",
                      "monthly_irregular_income")}
    if vals["monthly_fixed_income"] <= 0:
        abort(400, description="월 고정 수입은 0보다 커야 합니다.")
    m = body.get("m_multiplier")
    try:
        m = int(m) if m not in (None, "") else None
        profile = pe.FinancialProfile(vals["monthly_fixed_income"], vals["essential_expense"], vals["cash_current"],
                                      itype, monthly_irregular_income=vals["monthly_irregular_income"] or 0,
                                      monthly_debt_payment=vals["monthly_debt_payment"] or 0, m_multiplier=m)
        answers = {q["key"]: int(body.get("answers", {}).get(q["key"], -1)) for q in QUESTIONS}
        if any(v < 0 for v in answers.values()):
            abort(400, description="설문 5문항에 모두 답해 주세요.")
        goals = _build_goals(body.get("goals") or {})
        survey = pe.SurveyAnswers(**answers, goals=goals)
    except (ValueError, TypeError) as e:
        msg = str(e)
        known = any(w in msg for w in ("응답", "개월", "연도", "나이", "비율", "목표"))
        abort(400, description=msg if known else "설문 5문항에 모두 답해 주세요.")
    return profile, survey


def _build_goals(g: dict):
    """나이·목표 시점 입력 → LifeGoals (출생 연도를 비우면 목표 반영 없이 설문만 사용)"""
    def num(k, cast=int):
        v = g.get(k)
        if v in (None, ""):
            return None
        try:
            return cast(v)
        except (TypeError, ValueError):
            raise ValueError(f"목표 입력값을 확인해 주세요: {k}")
    birth = num("birth_year")
    if birth is None:
        if any(g.get(k) not in (None, "") for k in ("retirement_age", "home_year", "other_year")):
            raise ValueError("목표 시점을 반영하려면 출생 연도를 입력해 주세요.")
        return None
    this_year = pe.clock_today().year
    goals = []
    for key, default_name in (("home", "주택 구입"), ("other", "기타 목표")):
        year, share = num(f"{key}_year"), num(f"{key}_share", float)
        if year is None and share in (None, 0):
            continue
        name = (str(g.get(f"{key}_name") or "").strip() or default_name)[:20]
        if year is None or not share:
            raise ValueError(f"{name}: 목표 연도와 투자금 중 쓸 비율을 함께 입력해 주세요.")
        if not this_year <= year <= this_year + 60:
            raise ValueError(f"{name} 목표 연도는 {this_year}~{this_year + 60}년 사이로 입력해 주세요.")
        goals.append(pe.Goal(name, year, share, key))
    return pe.LifeGoals(birth, num("retirement_age"), tuple(goals))


def _goals_json(survey: pe.SurveyAnswers, risk: pe.RiskProfile, today: date) -> Optional[dict]:
    g = survey.goals
    if g is None:
        return None
    buckets = []
    for b in g.buckets(today):
        applied = min(risk.tier, b.cap)
        buckets.append({"name": b.name, "share": b.share, "years": b.years, "retired": b.retired,
                        "cap": b.cap, "capName": pe.TIER_NAMES[b.cap], "appliedTier": applied,
                        "appliedName": pe.TIER_NAMES[applied],
                        "horizonScore": (pe.RETIRED_HORIZON_SCORE if b.retired else
                                         survey.q2_1 if b.years is None else pe.goal_horizon_score(b.years))})
    targets = pe.goal_blended_targets(risk.tier, g, today)
    return {"age": g.age(today), "retirementAge": g.retirement_age, "retirementYear": g.retirement_year,
            "buckets": buckets, "goalScore": round(g.horizon_score(today, survey.q2_1), 1),
            "q2_1": survey.q2_1, "used": round(survey.horizon_q2_1(today), 1),
            "passed": g.passed(today),
            "targets": [{"name": c, "model": pe.MODEL_PORTFOLIOS[risk.tier].targets.get(c, 0),
                         "blended": round(targets.get(c, 0), 1)}
                        for c in pe.ASSET_CLASSES if targets.get(c) or pe.MODEL_PORTFOLIOS[risk.tier].targets.get(c)],
            "adjusted": any(abs(targets.get(c, 0) - pe.MODEL_PORTFOLIOS[risk.tier].targets.get(c, 0)) > 0.05
                            for c in pe.ASSET_CLASSES)}


def _explain(profile: pe.FinancialProfile, survey: pe.SurveyAnswers) -> dict:
    """등급 산출 과정을 단계별로 설명"""
    today = pe.clock_today()
    risk = pe.assess_risk(survey, profile.buffer, today)
    buf_score = pe.clamp(profile.buffer)
    def label(key, score):
        q = next(q for q in QUESTIONS if q["key"] == key)
        return next(t for v, t in q["options"] if v == score)
    tol_parts = [{"key": k, "label": label(k, getattr(survey, k)), "score": getattr(survey, k), "weight": w}
                 for k, w in (("q1_1", .40), ("q1_2", .35), ("q1_3", .25))]
    hor_parts = [{"key": k, "label": label(k, getattr(survey, k)), "score": getattr(survey, k), "weight": w}
                 for k, w in (("q2_1", .60), ("q2_2", .40))]
    q21_used = survey.horizon_q2_1(today)
    if survey.goals is not None and q21_used < survey.q2_1:        # 목표 시점이 더 가까우면 그 점수 사용
        hor_parts[0].update(label=hor_parts[0]["label"] + " → 목표 시점 기준으로 낮춤", score=round(q21_used, 1))
    buf = profile.buffer
    fin_rule = ("Buffer 10% 미만 → 최대 40점(안정추구형 이하)" if buf < 10 else
                "Buffer 10~20% → 최대 60점(위험중립형 이하)" if buf < 20 else "Buffer 20% 이상 → 제한 없음")
    tol = risk.tol
    psy_rule = ("Tol 20 이하 → 최대 20점(보수형)" if tol <= 20 else
                "Tol 20~40 → 최대 50점(위험중립형 이하)" if tol <= 40 else "Tol 40 초과 → 제한 없음")
    binding = min((("기본 점수", risk.base), ("재무 상한", risk.cap_financial), ("심리 상한", risk.cap_psychological)),
                  key=lambda x: x[1])[0]
    model = pe.MODEL_PORTFOLIOS[risk.tier]
    return {
        "stage1": {"incomeType": profile.income_type.label, "freeCash": round(profile.free_cash),
                   "buffer": round(buf, 1), "dti": round(profile.dti, 1) if profile.dti != float("inf") else None,
                   "adjDebt": round(profile.adj_debt), "m": profile.m_multiplier,
                   "reserve": round(profile.c_reserve), "cash": round(profile.cash_current),
                   "deployable": round(profile.cash_current - profile.c_reserve)},
        "tol": {"value": round(tol, 1), "parts": tol_parts},
        "horizon": {"value": round(risk.horizon, 1), "parts": hor_parts},
        "bufferScore": {"raw": round(buf, 1), "value": round(buf_score, 1)},
        "base": {"value": round(risk.base, 1),
                 "terms": [{"name": "Tol", "value": round(tol, 1), "weight": .5},
                           {"name": "Horizon", "value": round(risk.horizon, 1), "weight": .2},
                           {"name": "Buffer", "value": round(buf_score, 1), "weight": .3}]},
        "caps": {"financial": risk.cap_financial, "financialRule": fin_rule,
                 "psychological": risk.cap_psychological, "psychologicalRule": psy_rule, "binding": binding},
        "final": {"score": round(risk.final, 2), "tier": risk.tier, "name": pe.TIER_NAMES[risk.tier],
                  "range": pe.tier_range_label(risk.tier)},
        "portfolio": {"name": model.name, "purpose": model.purpose,
                      "items": [{"name": n, "assetClass": c, "weight": w} for n, c, w in model.items]},
        "goals": _goals_json(survey, risk, today),
    }


@app.get("/api/onboarding")
def onboarding_info():
    with _lock:
        p, sv = STATE.profile, STATE.survey
        return jsonify(
            questions=[{"key": q["key"], "group": q["group"], "weight": q["weight"], "title": q["title"],
                        "options": [{"score": v, "label": t} for v, t in q["options"]]} for q in QUESTIONS],
            incomeTypes=[{"key": t.name, "label": t.label, "mMin": t.m_min, "mMax": t.m_max} for t in pe.IncomeType],
            current={"monthly_fixed_income": p.monthly_fixed_income, "essential_expense": p.essential_expense,
                     "cash_current": p.cash_current, "monthly_debt_payment": p.monthly_debt_payment,
                     "monthly_irregular_income": p.monthly_irregular_income, "income_type": p.income_type.name,
                     "m_multiplier": p.m_multiplier,
                     "answers": {q["key"]: getattr(sv, q["key"]) for q in QUESTIONS},
                     "goals": _goals_input(sv.goals)})


def _goals_input(g) -> dict:
    if g is None:
        return {}
    out = {"birth_year": g.birth_year, "retirement_age": g.retirement_age}
    for goal in g.goals:
        key = goal.kind if goal.kind in ("home", "other") else "other"
        out.update({f"{key}_name": goal.name, f"{key}_year": goal.year, f"{key}_share": goal.share})
    return out


@app.post("/api/onboarding/evaluate")
def onboarding_evaluate():
    """진단만 (서버 상태 변경 없음)"""
    profile, survey = _build_onboarding(request.get_json(silent=True) or {})
    return jsonify(_explain(profile, survey))


@app.post("/api/onboarding/apply")
def onboarding_apply():
    """진단 결과를 내 등급으로 적용: 목표 비중·필수 비상금이 새 기준으로 바뀜"""
    profile, survey = _build_onboarding(request.get_json(silent=True) or {})
    with _lock:
        old_tier = STATE.manager.current_tier
        portfolio, seasonal = STATE.manager.portfolio, STATE.manager.seasonal
        m = pe.PortfolioManager(profile, survey, portfolio, pe.demo_instruments())
        m.seasonal = seasonal
        m.last_emergency_balance = profile.cash_current
        STATE.profile, STATE.survey, STATE.manager = profile, survey, m
        expired = 0
        for p in STATE.proposals.values():           # 이전 등급 기준 제안은 더 이상 유효하지 않음
            if p["status"] == "승인 대기":
                p["status"] = "만료"
                expired += 1
        STATE.audit.append("투자 등급 변경", before=old_tier, after=m.current_tier,
                           score=round(m.risk.final, 2), expired_proposals=expired)
        return jsonify(result=_explain(profile, survey), expiredProposals=expired)



# ════════════════════════════════════════════════════════════════════
# 일일 가계부 기록 (매일의 수입·지출 → 자동 분류 → 월 합계)
# ════════════════════════════════════════════════════════════════════
ENTRY_KINDS = {"expense": "출금", "income": "입금", "emg_in": "출금", "emg_out": "입금"}
OVERRIDES = {"auto": None, "essential": True, "nonessential": False, "regular": True, "irregular": False,
             "exclude": "exclude"}
OVERRIDE_LABEL = {"essential": "필수 지출(직접 지정)", "nonessential": "비필수 지출(직접 지정)",
                  "regular": "정기 수입(직접 지정)", "irregular": "비정기 수입(직접 지정)",
                  "exclude": "집계 제외(직접 지정)"}


def _month_review(year: int, month: int):
    """해당 월 기록을 엔진 분류기로 분류하고, 사용자가 직접 지정한 분류를 덮어씀"""
    period = _period(year, month)
    rows = [(eid, e) for eid, e in STATE.entries.items()
            if e["tx"].tx_date.year == year and e["tx"].tx_date.month == month]
    review = pe.MonthlyLedgerReview(period, [e["tx"] for _, e in rows], STATE.classifier)
    for eid, e in rows:
        ov = e["override"]
        if ov != "auto":
            it = review.items[e["tx"].tx_id]
            it.include = None if ov == "exclude" else OVERRIDES[ov]
            it.label, it.confidence, it.emergency = OVERRIDE_LABEL[ov], "사용자 지정", 0
    return review, rows


def _entry_json(eid: int, e: dict, item) -> dict:
    tx = e["tx"]
    if item.emergency:
        cls = "비상금 적립" if item.emergency > 0 else "비상금 인출"
    elif item.include is None:
        cls = "집계 제외"
    elif tx.kind == "출금":
        cls = "필수" if item.include else "비필수"
    else:
        cls = "정기 수입" if item.include else "비정기 수입"
    return {"id": eid, "date": tx.tx_date.isoformat(), "kind": "income" if tx.kind == "입금" else "expense",
            "amount": tx.amount, "description": tx.description, "class": cls, "label": item.label,
            "confidence": item.confidence, "override": e["override"], "merchant": item.merchant}


def _entries_payload(year: int, month: int) -> dict:
    review, rows = _month_review(year, month)
    entries = [_entry_json(eid, e, review.items[e["tx"].tx_id]) for eid, e in rows]
    entries.sort(key=lambda x: (x["date"], x["id"]))
    irregular_items = [it for it in review.items.values()
                       if it.tx.kind == "입금" and it.include is False and not it.emergency]
    irregular = sum(it.tx.amount for it in irregular_items)
    taxable = sum(it.tx.amount for it in irregular_items
                  if any(k in it.tx.description for k in pe.TAXABLE_IRREGULAR_KEYWORDS) or "사업" in it.label)
    summary = {"count": len(entries), "confirmedIncome": round(review.confirmed_income),
               "irregularIncome": round(irregular), "irregularTaxable": round(taxable),
               "totalExpense": round(review.total_expense),
               "essentialExpense": round(review.essential_expense),
               "emergencyDeposit": round(review.emergency_deposit),
               "emergencyWithdrawal": round(review.emergency_withdrawal),
               "needsReview": len(review.needs_review())}
    summary["net"] = summary["confirmedIncome"] + summary["irregularIncome"] - summary["totalExpense"]
    return {"entries": entries, "summary": summary}


def _parse_entry(body: dict) -> tuple:
    kind = body.get("kind")
    if kind not in ENTRY_KINDS:
        abort(400, description="구분을 선택해 주세요 (지출·수입·비상금 적립·비상금 인출).")
    try:
        day = date.fromisoformat(body.get("date", ""))
    except ValueError:
        abort(400, description="날짜 형식이 올바르지 않습니다.")
    amount = _num(body, "amount", required=True)
    if amount <= 0:
        abort(400, description="금액은 0보다 커야 합니다.")
    desc = str(body.get("description", "")).strip()
    if kind == "emg_in":
        desc = "비상금 적립" + (f" ({desc})" if desc else "")
    elif kind == "emg_out":
        desc = "비상금 인출" + (f" ({desc})" if desc else "")
    if not desc or len(desc) > 40:
        abort(400, description="내용(가맹점·메모)을 1~40자로 입력해 주세요.")
    override = body.get("override", "auto")
    if override not in OVERRIDES:
        abort(400, description="분류 값이 올바르지 않습니다.")
    if kind.startswith("emg"):
        override = "auto"
    elif kind == "expense" and override in ("regular", "irregular"):
        abort(400, description="지출에는 필수·비필수 분류만 쓸 수 있어요.")
    elif kind == "income" and override in ("essential", "nonessential"):
        abort(400, description="수입에는 정기·비정기 분류만 쓸 수 있어요.")
    return day, ENTRY_KINDS[kind], amount, desc, override


def _learn(e: dict, remember: bool) -> None:
    """'같은 가맹점에 계속 적용' → 엔진 분류기에 가맹점 규칙으로 기억"""
    ov = e["override"]
    if remember and ov not in ("auto", "exclude"):
        tx = e["tx"]
        STATE.classifier.learn(tx, _period(tx.tx_date.year, tx.tx_date.month), OVERRIDES[ov],
                               OVERRIDE_LABEL[ov].replace("(직접 지정)", ""), pe.SCOPE_MERCHANT)


@app.get("/api/entries")
def list_entries():
    try:
        year, month = int(request.args["year"]), int(request.args["month"])
        assert 1 <= month <= 12
    except (KeyError, ValueError, AssertionError):
        abort(400, description="year, month 가 올바르지 않습니다.")
    with _lock:
        return jsonify(_entries_payload(year, month))


@app.post("/api/entries")
def add_entry():
    body = request.get_json(silent=True) or {}
    day, kind, amount, desc, override = _parse_entry(body)
    with _lock:
        eid = STATE.add_entry(day, kind, amount, desc, override)
        _learn(STATE.entries[eid], bool(body.get("remember")))
        review, _ = _month_review(day.year, day.month)
        out = _entry_json(eid, STATE.entries[eid], review.items[f"E{eid}"])
        # 큰 출금(대형 결제·비상금 인출 포함)을 기록하면 즉시 트리거 스캔
        if kind == "출금" or out["class"] == "비상금 인출":
            if amount >= _large_threshold() or out["class"] == "비상금 인출":
                scan = run_trigger_scan("대형 출금·결제 기록")
                out["scan"] = {"active": scan["active"], "proposalId": scan["proposalId"]}
        return jsonify(out), 201


@app.patch("/api/entries/<int:eid>")
def update_entry(eid: int):
    body = request.get_json(silent=True) or {}
    with _lock:
        e = STATE.entries.get(eid)
        if not e:
            abort(404, description="해당 기록이 없습니다.")
        ov = body.get("override", "auto")
        kind = "income" if e["tx"].kind == "입금" else "expense"
        if ov not in OVERRIDES or (kind == "expense" and ov in ("regular", "irregular")) \
                or (kind == "income" and ov in ("essential", "nonessential")):
            abort(400, description="분류 값이 올바르지 않습니다.")
        e["override"] = ov
        _learn(e, bool(body.get("remember")))
        d = e["tx"].tx_date
        review, _ = _month_review(d.year, d.month)
        return jsonify(_entry_json(eid, e, review.items[e["tx"].tx_id]))


@app.delete("/api/entries/<int:eid>")
def delete_entry(eid: int):
    with _lock:
        if eid not in STATE.entries:
            abort(404, description="해당 기록이 없습니다.")
        del STATE.entries[eid]
        return ("", 204)



# ════════════════════════════════════════════════════════════════════
# 실시간 트리거 감시 (Trigger A·B·C → 목표 비중 조절 모드)
#   스캔 시점: 앱 접속 · 큰 지출 기록(대형 결제) · 매일 07:00 정기 스캔 · '지금 스캔' 버튼 · 월 마감
# ════════════════════════════════════════════════════════════════════
DAILY_SCAN_TIME = (7, 0)
MONITOR = {"last": None, "next": None, "history": []}


def _live_snapshot(today: date) -> pe.LedgerSnapshot:
    """
    지금 시점의 판단 기준 (엔진 LiveLedger 와 같은 원칙)
      수입      : 이번 달 기록된 정기 수입, 아직 없으면(급여 전) 평소 월 고정 수입
      필수 지출 : max(평소 필수 지출, 이번 달 기록된 필수 지출) — 월초 오판 방지, 월중 급증은 반영
      비상금    : 이번 달 가계부에 저장한 잔액이 있으면 그 값,
                  없으면 마지막 확정 잔액 + 이번 달 비상금 적립 − 인출 (+ 시스템 이체)
      목돈 지출 : 오늘부터 30일 안의 '목돈' 지출 일정 합계와 가장 가까운 D-Day
    """
    m = STATE.manager
    review, _ = _month_review(today.year, today.month)
    income = review.confirmed_income or STATE.profile.monthly_fixed_income
    essential = max(STATE.profile.essential_expense, review.essential_expense)
    L = STATE.ledgers.get(_period(today.year, today.month), {})
    if L.get("emergency_balance") is not None:
        balance, source = L["emergency_balance"], "이번 달 가계부에 저장한 잔액"
    else:
        balance = (m.last_emergency_balance or 0) + getattr(m, "pending_emergency_transfer", 0.0) \
            + review.emergency_deposit - review.emergency_withdrawal
        source = "마지막 확정 잔액 + 이번 달 비상금 적립·인출"
    cf, dday, bdays, due, _ = pe.upcoming_big_expenses(STATE.calendar.big_events(), today)
    snap = pe.LedgerSnapshot(income, essential, balance, review.emergency_deposit, review.emergency_withdrawal,
                             upcoming_cf=cf, dday=dday, bdays=bdays, due_date=due, as_of=today,
                             period=_period(today.year, today.month), balance_source=source,
                             total_expense=review.total_expense)
    snap.expense_reserved = getattr(m, "expense_reserve", 0.0)
    return snap


def _trigger_status(snap: pe.LedgerSnapshot) -> dict:
    """트리거별 판단 근거 (화면 표시용)"""
    m = STATE.manager
    reserve = m.c_reserve(snap.essential_expense)
    raw = pe.detect_triggers(snap, reserve, m.buffer_old)
    latch = m.latch_status(snap, reserve, pe.clock_today())
    active = {t for t, k in ((pe.Trigger.A, "A"), (pe.Trigger.B, "B"), (pe.Trigger.C, "C"))
              if t in raw or latch[k]["phase"] != "정상"}
    cf_cover = snap.c_current + snap.expense_reserved
    status = {
        "A": {"name": "비상금 침범", "active": pe.Trigger.A in active,
              "balance": round(snap.c_current), "required": round(reserve),
              "shortage": round(max(0.0, reserve - snap.c_current)), "source": snap.balance_source,
              "releaseLine": round(reserve * pe.A_RELEASE_RATIO),
              "rule": "비상금 계좌 잔액 < 필수 비상금"},
        "B": {"name": "재무 잉여율 위기", "active": pe.Trigger.B in active,
              "buffer": round(snap.buffer, 1), "baseline": round(m.buffer_old, 1),
              "half": round(m.buffer_old * 0.5, 1), "income": round(snap.monthly_income),
              "essential": round(snap.essential_expense),
              "level": {"B-1": "B-1 (Buffer 10% 미만에서 시작)", "B-2": "B-2 (기준의 50% 이하에서 시작)",
                        "B-2 부분 회복": "B-2 부분 회복 (원래 등급 복귀 대기)"}.get(latch["B"]["phase"],
                       "B-1 (Buffer 10% 미만)" if snap.buffer < 10 else
                       "B-2 (기준의 50% 이하)" if pe.Trigger.B in raw else ""),
              "rule": "Buffer < 10% 또는 Buffer ≤ 기준 Buffer의 50%"},
        "C": {"name": "단기 목돈 지출", "active": pe.Trigger.C in active,
              "upcoming": round(snap.upcoming_cf), "dday": snap.dday, "cover": round(cf_cover),
              "dueDate": snap.due_date.isoformat() if snap.due_date else None,
              "businessDays": snap.bdays,
              "reserved": round(snap.expense_reserved),
              "shortage": round(max(0.0, snap.upcoming_cf - cf_cover)),
              "releaseLine": round(snap.upcoming_cf * pe.C_RELEASE_RATIO),
              "rule": f"{pe.C_WINDOW_DAYS}일 안 목돈 지출 > 비상금 잔액 + 이미 확보한 지출 대기 현금"},
    }
    for k in status:                              # 해제 대기: 진입 기준은 벗어났지만 해제 조건·최소 유지 기간 미충족
        status[k].update(phase=latch[k]["phase"], release=latch[k]["release"],
                         progress=latch[k]["progress"], reentryLevel=latch[k]["level"])
    return status


def _register_proposal(proposal: pe.OrderProposal, period: str, log: list, origin: str):
    if not proposal.orders:
        return None
    pe.schedule_orders(proposal.orders, STATE.manager.portfolio, pe.clock_today(), STATE.manager.instruments)
    pid = STATE.next_id()
    created = pe.clock_now().replace(microsecond=0)
    fp = fingerprint(pid, created, proposal.orders)
    STATE.proposals[pid] = {"proposal": proposal, "status": "승인 대기", "period": period, "log": log,
                            "created": created, "fingerprint": fp, "origin": origin}
    STATE.audit.append("제안 생성", id=pid, origin=origin, orders=len(proposal.orders),
                       total=round(order_total(proposal.orders)), fingerprint=fp[:16])
    return pid


def run_trigger_scan(source: str) -> dict:
    """트리거 스캔 실행 → 발동 시 엔진의 목표 비중 조절 모드 작동 (호출 전 _lock 보유 필요)"""
    today = pe.clock_today()
    snap = _live_snapshot(today)
    before = {"tier": STATE.manager.current_tier, "targets": dict(STATE.manager.targets)}
    log, proposal = STATE.manager.event_scan(snap, source, today)
    pid = _register_proposal(proposal, _period(today.year, today.month), log, f"트리거 대응 ({source})")
    status = _trigger_status(snap)
    result = {"at": pe.clock_now().isoformat(timespec="seconds"), "source": source,
              "active": [k for k, v in status.items() if v["active"]], "status": status,
              "log": log, "proposalId": pid,
              "tierChanged": before["tier"] != STATE.manager.current_tier}
    MONITOR["last"] = result
    MONITOR["history"] = ([{"at": result["at"], "source": source, "active": result["active"]}]
                          + MONITOR["history"])[:20]
    if result["active"]:
        STATE.audit.append("트리거 감지", source=source, active=result["active"], proposal=pid)
    return result


def _mode_json() -> dict:
    """목표 비중 조절 모드 상태: 원래 등급·목표 vs 현재 적용 중인 등급·목표"""
    m = STATE.manager
    original = m._tier_targets(m.original_tier)
    frozen_reasons = []
    last = MONITOR["last"]
    act = set(last["active"]) if last else set()
    if "A" in act:
        frozen_reasons.append("비상금 침범 → 신규 매수 동결, 들어오는 돈은 비상금으로")
    if "C" in act:
        frozen_reasons.append("목돈 지출 임박 → 신규 매수 유예, 지출 자금 먼저 확보")
    if m.b1_active:
        frozen_reasons.append("B-1 → 위험 자산 신규 매수 동결, 현금 최우선 확보")
    elif getattr(m, "b2_active", False):
        frozen_reasons.append("B-2 → 주식 신규 매수 중단, 채권·현금성 자산만 매수")
    elif m.b2_applied_tier is not None:
        frozen_reasons.append("B-2 부분 회복 → 낮춘 등급으로 운용, 기준의 85% 이상 2개월 연속이면 원래 등급 복귀")
    if getattr(m, "ledger_frozen", False):
        frozen_reasons.append("가계부 연속 미입력 → 신규 매수 중단")
    return {
        "originalTier": {"level": m.original_tier, "name": pe.TIER_NAMES[m.original_tier]},
        "currentTier": {"level": m.current_tier, "name": pe.TIER_NAMES[m.current_tier]},
        "b1": m.b1_active, "b2": m.b2_applied_tier is not None,
        "targets": [{"name": c, "original": round(original.get(c, 0), 1), "current": round(m.targets.get(c, 0), 1)}
                    for c in pe.ASSET_CLASSES if original.get(c, 0) or m.targets.get(c, 0)],
        "adjusted": any(abs(original.get(c, 0) - m.targets.get(c, 0)) > 0.05 for c in pe.ASSET_CLASSES),
        "restrictions": frozen_reasons,
    }


@app.get("/api/triggers")
def triggers():
    with _lock:
        snap = _live_snapshot(pe.clock_today())
        return jsonify(status=_trigger_status(snap), last=MONITOR["last"], history=MONITOR["history"],
                       nextScheduled=MONITOR["next"], mode=_mode_json(),
                       largeTxThreshold=round(_large_threshold()))


@app.post("/api/triggers/scan")
def triggers_scan():
    body = request.get_json(silent=True) or {}
    source = {"app_open": "앱 실행", "manual": "지금 스캔"}.get(body.get("source"), "지금 스캔")
    with _lock:
        result = run_trigger_scan(source)
        return jsonify(result=result, mode=_mode_json())


def _large_threshold() -> float:
    return min(pe.LARGE_TX_MIN, pe.LARGE_TX_RATIO * STATE.profile.essential_expense)


def _scheduler():
    """매일 07:00 정기 스캔 (서버가 켜져 있는 동안)"""
    import time
    while True:
        now = pe.clock_now()
        nxt = now.replace(hour=DAILY_SCAN_TIME[0], minute=DAILY_SCAN_TIME[1], second=0, microsecond=0)
        if nxt <= now:
            nxt += timedelta(days=1)
        MONITOR["next"] = nxt.isoformat(timespec="minutes")
        time.sleep(max(1.0, (nxt - pe.clock_now()).total_seconds()))
        with _lock:
            run_trigger_scan("07:00 정기 업데이트")
            save_state("07:00 정기 업데이트")


if __name__ == "__main__":
    threading.Thread(target=_scheduler, daemon=True).start()
    app.run(host="127.0.0.1", port=int(os.environ.get("PORT", 5000)), debug=False)
