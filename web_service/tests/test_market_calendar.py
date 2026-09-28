"""한국·미국 공휴일, 증시 휴장일, T+N 정산일, 영업일 수"""
import unittest
from datetime import date

from tests.helpers import EngineTestCase, pe

D = date


class KoreanHolidays(EngineTestCase):
    def names(self, year):
        return {e.day: e.name for e in pe.BuiltinHolidayTable().fetch(year)}

    def test_substitute_holidays(self):
        h25, h26, h27 = self.names(2025), self.names(2026), self.names(2027)
        self.assertEqual(h25[D(2025, 3, 3)], "대체공휴일(삼일절)")
        self.assertEqual(h25[D(2025, 5, 6)], "대체공휴일(어린이날)")        # 어린이날 = 부처님오신날
        self.assertEqual(h26[D(2026, 5, 25)], "대체공휴일(부처님오신날)")
        self.assertEqual(h26[D(2026, 8, 17)], "대체공휴일(광복절)")
        self.assertEqual(h26[D(2026, 10, 5)], "대체공휴일(개천절)")
        self.assertEqual(h27[D(2027, 12, 27)], "대체공휴일(성탄절)")

    def test_special_days(self):
        self.assertIn(D(2026, 6, 3), self.names(2026))                       # 지방선거
        self.assertIn(D(2025, 1, 27), self.names(2025))                      # 임시공휴일


class MarketClosures(EngineTestCase):
    def setUp(self):
        super().setUp()
        self.cal = pe.market_calendar()

    def test_krx_rules(self):
        kr25 = self.cal.closures("KR", 2025)
        self.assertEqual(kr25[D(2025, 5, 1)], "근로자의 날 휴장")
        self.assertEqual(kr25[D(2025, 12, 31)], "연말 휴장일")
        # 12/31이 토요일이면 직전 영업일(12/30 금) 휴장
        self.assertEqual(self.cal.closures("KR", 2022)[D(2022, 12, 30)], "연말 휴장일")

    def test_nyse_rules(self):
        us26 = self.cal.closures("US", 2026)
        self.assertIn(D(2026, 4, 3), us26)                                   # 성금요일
        self.assertIn(D(2026, 7, 3), us26)                                   # 독립기념일(토) → 금요일
        self.assertIn(D(2026, 11, 26), us26)                                 # 추수감사절
        self.assertNotIn(D(2026, 10, 12), us26)                              # 콜럼버스 데이: 증시는 개장
        self.assertNotIn(D(2021, 12, 31), self.cal.closures("US", 2021))     # 신정(토)은 대체 휴장 없음
        self.assertIn(D(2025, 1, 9), self.cal.closures("US", 2025))          # 국가 애도일(임시 휴장)

    def test_us_settlement_holidays(self):
        settle = self.cal.us_settlement_holidays(2026)
        self.assertIn(D(2026, 10, 12), settle)                               # 콜럼버스 데이
        self.assertIn(D(2026, 11, 11), settle)                               # 재향군인의 날

    def test_easter(self):
        self.assertEqual(pe._easter(2024), D(2024, 3, 31))
        self.assertEqual(pe._easter(2026), D(2026, 4, 5))


class Settlement(EngineTestCase):
    def setUp(self):
        super().setUp()
        self.cal = pe.market_calendar()

    def check(self, market, n, order_day, expected):
        self.assertEqual(self.cal.cash_available(market, n, order_day), expected)

    def test_korea(self):
        self.check("KR", 2, D(2026, 9, 18), D(2026, 9, 22))                  # 주말 건너뜀
        self.check("KR", 2, D(2026, 9, 23), D(2026, 9, 29))                  # 추석 연휴
        self.check("KR", 2, D(2026, 9, 26), D(2026, 9, 30))                  # 토요일 주문 → 월요일 체결
        self.check("KR", 2, D(2026, 12, 30), D(2027, 1, 5))                  # 연말 휴장·신정

    def test_us_then_next_korean_business_day(self):
        self.check("US", 1, D(2026, 10, 9), D(2026, 10, 14))                 # 콜럼버스 결제 휴무
        self.check("US", 1, D(2026, 11, 25), D(2026, 11, 30))                # 추수감사절
        self.check("US", 1, D(2026, 11, 26), D(2026, 12, 1))

    def test_cash_is_instant(self):
        self.check(None, 0, D(2026, 9, 26), D(2026, 9, 26))

    def test_business_days_until(self):
        self.assertEqual(self.cal.business_days_until(D(2026, 9, 23), D(2026, 10, 30)), 23)
        self.assertEqual(self.cal.business_days_until(D(2026, 9, 23), D(2026, 9, 28)), 1)
        self.assertEqual(self.cal.business_days_until(D(2026, 9, 23), D(2026, 9, 20)), -1)


class CalendarDisplay(EngineTestCase):
    def test_month_events(self):
        ev = pe.market_calendar().month_events(2026, 12)
        got = {(e["date"], e["market"], e["kind"]) for e in ev}
        self.assertIn(("2026-12-25", "KR", "휴장"), got)
        self.assertIn(("2026-12-25", "US", "휴장"), got)
        self.assertIn(("2026-12-31", "KR", "휴장"), got)


if __name__ == "__main__":
    unittest.main()
