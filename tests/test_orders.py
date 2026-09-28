"""매매 제안의 집행일·대금 입금일 (휴장일 반영)과 유동성 매도 즉시 발주"""
import unittest
from datetime import date

from tests.helpers import ESSENTIAL, EngineTestCase, pe


class Scheduling(EngineTestCase):
    def test_liquidity_sells_go_out_immediately(self):
        m = self.manager()
        s = pe.LedgerSnapshot(4e6, ESSENTIAL, 10_400_000, upcoming_cf=30e6, dday=23, bdays=15,
                              due_date=date(2026, 10, 20), as_of=date(2026, 9, 23))
        plan = pe.handle_trigger_c(s, m.portfolio, m.targets)
        self.assertTrue(plan.orders)
        self.assertTrue(all(o.day == 0 for o in plan.orders))       # T+N 예약이 아니라 즉시

    def test_exec_and_cash_dates_skip_holidays(self):
        m = self.manager()
        s = pe.LedgerSnapshot(4e6, ESSENTIAL, 10_400_000, upcoming_cf=30e6, dday=23, bdays=15,
                              due_date=date(2026, 10, 20), as_of=date(2026, 9, 23))
        orders = pe.handle_trigger_c(s, m.portfolio, m.targets).orders
        pe.schedule_orders(orders, m.portfolio, date(2026, 9, 23), m.instruments)
        for o in orders:
            self.assertEqual(o.exec_date, date(2026, 9, 23))
            self.assertEqual(o.cash_date, date(2026, 9, 29))        # 추석 연휴 뒤
            self.assertIn("대금 09/29(화)", str(o))

    def test_weekend_proposal_executes_next_business_day(self):
        m = self.manager()
        s = pe.LedgerSnapshot(4e6, ESSENTIAL, 10_400_000, upcoming_cf=30e6, dday=23, bdays=15,
                              due_date=date(2026, 10, 20), as_of=date(2026, 10, 3))
        orders = pe.handle_trigger_c(s, m.portfolio, m.targets).orders
        pe.schedule_orders(orders, m.portfolio, date(2026, 10, 3), m.instruments)   # 토요일
        self.assertTrue(all(o.exec_date == date(2026, 10, 6) for o in orders))     # 10/5 대체공휴일


if __name__ == "__main__":
    unittest.main()
