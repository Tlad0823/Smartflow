"""트리거 진입·해제 기준 분리, 최소 유지 기간, 강한 회복, 재진입 대기, Trigger C 감시 기간"""
import unittest
from datetime import date, timedelta

from tests.helpers import ESSENTIAL, EngineTestCase, MonthRunner, has, income_for, pe


class TriggerA(EngineTestCase):
    def test_release_after_7_days_at_105pct(self):
        m = self.manager()
        r = MonthRunner(m)
        r.close(bal=r.reserve * 0.8)
        self.assertEqual(r.state("A"), (True, 0))
        start, released = m.clock, None
        for i in range(1, 9):
            s = pe.LedgerSnapshot(income_for(35), ESSENTIAL, emergency_balance=r.reserve * 1.06)
            m.event_scan(s, "daily", start + timedelta(days=i))
            if not m.latches["A"].active and released is None:
                released = i
        self.assertEqual(released, 7)

    def test_104pct_is_not_enough(self):
        m = self.manager()
        r = MonthRunner(m)
        r.close(bal=r.reserve * 0.8)
        r.close(bal=r.reserve * 1.04)
        self.assertTrue(r.state("A")[0])

    def test_month_close_confirms_release(self):
        m = self.manager()
        r = MonthRunner(m)
        r.close(bal=r.reserve * 0.8)
        r.close(bal=r.reserve * 1.06)
        self.assertFalse(r.state("A")[0])

    def test_reentry_raises_level_and_blocks_month_close_release(self):
        m = self.manager()
        r = MonthRunner(m)
        r.close(bal=r.reserve * 0.8)
        r.close(bal=r.reserve * 1.06)                     # 해제
        log = r.close(bal=r.reserve * 0.9)                # 31일 안에 재진입
        self.assertEqual(r.state("A"), (True, 1))
        self.assertTrue(has(log, "재진입"))
        r.close(bal=r.reserve * 1.2)                      # 재진입 단계: 월 마감만으로는 해제 안 됨
        self.assertTrue(r.state("A")[0])


class TriggerB1(EngineTestCase):
    def test_needs_12pct_and_3_months(self):
        m = self.manager()
        r = MonthRunner(m)
        r.close(buf=8)
        self.assertTrue(m.b1_active)
        r.close(buf=11)                                   # 진입 후 1개월, 12% 미만: 유지
        self.assertTrue(m.b1_active)
        r.close(buf=12)
        self.assertTrue(m.b1_active)                      # 진입 후 2개월: 최소 유지 기간 전
        r.close(buf=12)
        self.assertFalse(m.b1_active)                     # 진입 후 3개월 + 12% 이상 → 해제

    def test_strong_recovery_releases_early(self):
        m = self.manager()
        r = MonthRunner(m)
        r.close(buf=8)
        r.close(buf=31)
        self.assertTrue(m.b1_active)
        log = r.close(buf=31)                             # 기준의 85% 이상 2개월 연속
        self.assertFalse(m.b1_active)
        self.assertTrue(has(log, "강한 회복"))


class TriggerB2(EngineTestCase):
    def test_partial_then_full_return(self):
        m = self.manager()
        r = MonthRunner(m)
        r.close(buf=15)                                   # 기준 35%의 50% 이하
        self.assertTrue(m.b2_active)
        for _ in range(2):
            r.close(buf=22)
        self.assertTrue(m.b2_active)                      # 60% 초과 2개월이지만 최소 3개월 미충족
        r.close(buf=22)
        self.assertFalse(m.b2_active)                     # 부분 회복
        self.assertIsNotNone(m.b2_applied_tier)
        for b in (25, 30, 30):
            r.close(buf=b)
        self.assertIsNone(m.b2_applied_tier)              # 85% 이상 2개월 → 원래 등급

    def test_strong_recovery_before_3_months(self):
        m = self.manager()
        r = MonthRunner(m)
        r.close(buf=15)
        r.close(buf=30)
        log = r.close(buf=30)
        self.assertFalse(m.b2_active)
        self.assertIsNone(m.b2_applied_tier)
        self.assertTrue(has(log, "강한 회복"))

    def test_reentry_extends_min_hold_to_6_months(self):
        m = self.manager()
        r = MonthRunner(m)
        r.close(buf=15)
        r.close(buf=30)
        r.close(buf=30)                                   # 해제
        r.close(buf=15)                                   # 31일 안에 재진입
        self.assertEqual(r.state("B2"), (True, 1))
        self.assertEqual(pe.B_HOLD_MONTHS[1], 6)


class TriggerC(EngineTestCase):
    def test_calendar_30_day_window(self):
        today = date(2026, 9, 23)
        ev = [("A", 1e6, date(2026, 10, 23)), ("B", 2e6, date(2026, 10, 24)), ("C", 3e6, date(2026, 9, 28))]
        total, dday, bdays, due, near = pe.upcoming_big_expenses(ev, today)
        self.assertEqual(total, 4e6)                      # D-30 포함, D-31 제외
        self.assertEqual((dday, bdays, due), (5, 1, date(2026, 9, 28)))
        self.assertEqual({n for n, *_ in near}, {"A", "C"})

    def test_detect_window_boundary(self):
        base = dict(upcoming_cf=16e6, due_date=date(2026, 10, 24), as_of=date(2026, 9, 23))
        s30 = pe.LedgerSnapshot(4e6, ESSENTIAL, 10_400_000, dday=30, bdays=21, **base)
        s31 = pe.LedgerSnapshot(4e6, ESSENTIAL, 10_400_000, dday=31, bdays=21, **base)
        self.assertIn(pe.Trigger.C, pe.detect_triggers(s30, 10_400_000, 35))
        self.assertNotIn(pe.Trigger.C, pe.detect_triggers(s31, 10_400_000, 35))
        s_past = pe.LedgerSnapshot(4e6, ESSENTIAL, 10_400_000, dday=-1, upcoming_cf=16e6)
        self.assertNotIn(pe.Trigger.C, pe.detect_triggers(s_past, 10_400_000, 35))

    def test_sell_candidates_filtered_by_real_cash_date(self):
        m = self.manager()
        s = pe.LedgerSnapshot(4e6, ESSENTIAL, 10_400_000, upcoming_cf=16e6, dday=5, bdays=1,
                              due_date=date(2026, 9, 28), as_of=date(2026, 9, 23))
        plan = pe.handle_trigger_c(s, m.portfolio, m.targets)
        for sc in plan.scores:
            if sc.holding.settlement_days >= 2:           # 추석 때문에 9/29 입금 → 9/28 지출에 못 맞춤
                self.assertIn("현금화 09/29", sc.excluded)
        self.assertEqual(s.dday_label(), "D-5 · 영업일 1일 · 09/28(월)")


if __name__ == "__main__":
    unittest.main()
