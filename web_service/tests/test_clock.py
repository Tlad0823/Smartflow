"""날짜 주입: 엔진·웹 서비스가 실제 오늘이 아니라 주입된 시계를 따르는지"""
import unittest
from datetime import date, datetime, timedelta

from tests.helpers import EngineTestCase, MonthRunner, fresh_client, pe


class ClockBasics(EngineTestCase):
    def test_engine_uses_injected_clock(self):
        self.assertEqual(pe.clock_today(), self.TODAY)
        self.clock.advance(days=10)
        self.assertEqual(pe.clock_today(), self.TODAY + timedelta(days=10))

    def test_frozen_clock_restores_previous(self):
        with pe.frozen_clock(date(2020, 3, 2)):
            self.assertEqual(pe.clock_today(), date(2020, 3, 2))
        self.assertEqual(pe.clock_today(), self.TODAY)

    def test_offset_clock_flows_from_start(self):
        clk = pe.OffsetClock(datetime(2021, 5, 3, 11, 0))
        self.assertLess(abs((clk.now() - datetime(2021, 5, 3, 11, 0)).total_seconds()), 5)

    def test_trading_window_follows_holidays(self):
        self.assertTrue(pe.is_trading_window(datetime(2026, 9, 23, 11)))       # 평일
        self.assertFalse(pe.is_trading_window(datetime(2026, 9, 24, 11)))      # 추석
        self.assertFalse(pe.is_trading_window(datetime(2026, 9, 23, 16)))      # 장 마감 후

    def test_goal_horizon_uses_clock(self):
        goals = pe.LifeGoals(1992, 60, (pe.Goal("주택 구입", 2029, 80, "home"),))
        sv = pe.SurveyAnswers(50, 66, 66, 75, 66, goals=goals)
        with pe.frozen_clock(date(2020, 1, 1)):
            far = sv.horizon_at()
        with pe.frozen_clock(date(2028, 1, 1)):              # 목표까지 1년 → 투자 기간 점수 하락
            near = sv.horizon_at()
        self.assertGreater(far, near)


class EarlyMonthClose(EngineTestCase):
    """월말 전에 미리 마감해도 판단일이 미래(다음 달 1일)로 가지 않아야 함"""
    TODAY = date(2026, 9, 27)

    def test_close_with_today_keeps_real_date(self):
        m = self.manager()
        r = MonthRunner(m, 2026)
        r.n = 8                                                  # 다음 마감 = 2026-09
        m.monthly_cycle(r.snap(bal=r.reserve * 0.8), today=pe.clock_today())
        self.assertEqual(m.clock, date(2026, 9, 27))
        self.assertTrue(m.latches["A"].active)

    def test_daily_scans_after_early_close_count_forward(self):
        m = self.manager()
        r = MonthRunner(m, 2026)
        r.n = 8
        m.monthly_cycle(r.snap(bal=r.reserve * 0.8), today=pe.clock_today())
        released_on = None
        for i in range(1, 10):
            day = self.TODAY + timedelta(days=i)
            s = pe.LedgerSnapshot(r.snap().monthly_income, 2_600_000, emergency_balance=r.reserve * 1.06)
            m.event_scan(s, "daily", day)
            if not m.latches["A"].active and released_on is None:
                released_on = i
        self.assertEqual(released_on, 7)                         # 105% 이상 7일째 해제

    def test_without_today_uses_period_end(self):
        m = self.manager()
        r = MonthRunner(m, 2026)
        r.n = 8
        m.monthly_cycle(r.snap())
        self.assertEqual(m.clock, date(2026, 10, 1))             # 시뮬레이션·데모 호환


class WebServiceClock(EngineTestCase):
    TODAY = date(2026, 9, 27)

    def test_close_month_uses_clock_date(self):
        c = fresh_client()
        L = {"monthly_income": 4_000_000, "total_expense": 2_600_000, "essential_expense": 2_600_000,
             "emergency_balance": 12_000_000}
        self.assertEqual(c.put("/api/ledger/2026-09", json=L).status_code, 200)
        self.assertEqual(c.post("/api/ledger/2026-09/close").status_code, 200)
        from tests.helpers import web
        self.assertEqual(web.STATE.manager.clock, date(2026, 9, 27))
        for p in c.get("/api/proposals").get_json():
            for o in p["orders"]:
                if o["execDate"] and o["assetClass"] != pe.CASH:     # 현금성 이체는 휴일에도 가능
                    self.assertGreaterEqual(o["execDate"], "2026-09-28")   # 일요일 → 다음 영업일

    def test_big_event_dday_relative_to_clock(self):
        c = fresh_client()
        c.post("/api/events", json={"date": "2026-10-20", "name": "이사 잔금", "amount": 30_000_000, "big": True})
        ev = [e for e in c.get("/api/calendar?year=2026&month=10").get_json()["events"] if e["big"]][0]
        self.assertEqual(ev["dday"], 23)
        self.assertEqual(ev["bdays"], 15)


if __name__ == "__main__":
    unittest.main()
