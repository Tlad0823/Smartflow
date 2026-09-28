"""승인 시점 재계산: 날짜를 다시 계산하고, 지출일을 넘기게 된 매도는 확인을 받는지"""
import unittest
from datetime import date, datetime

from tests.helpers import EngineTestCase, fresh_client, pe, web

PIN = "135790"


class ApprovalRecalc(EngineTestCase):
    TODAY = date(2026, 9, 23)              # 수요일, 다음 날부터 추석 연휴

    def setUp(self):
        super().setUp()
        self.clock.set(datetime(2026, 9, 23, 11, 0))
        self.c = fresh_client()
        web.STATE.guard.per_order = web.STATE.guard.daily = 100_000_000   # 이 테스트는 한도가 아니라 날짜 확인이 목적
        # 9/29(화) 지출 → 오늘 오전 매도하면 T+2 대금 9/29 입금 (간신히 맞춤)
        self.c.post("/api/events", json={"date": "2026-09-29", "name": "이사 잔금", "amount": 30_000_000, "big": True})
        self.c.post("/api/triggers/scan", json={"source": "manual"})
        self.p = self.pending()

    def pending(self):
        ps = [p for p in self.c.get("/api/proposals").get_json() if p["status"] == "승인 대기"]
        self.assertTrue(ps, "트리거 대응 제안이 만들어져야 해요")
        return ps[0]

    def approve(self, **extra):
        body = {"fingerprint": self.p["fingerprint"], "pin": PIN, **extra}
        return self.c.post(f"/api/proposals/{self.p['id']}/approve", json=body,
                           headers={"Idempotency-Key": f"k-{datetime.now().timestamp()}"})

    def sells(self, p):
        return [o for o in p["orders"] if o["side"] == "매도" and o["dueDate"]]

    def test_on_time_no_warning(self):
        self.assertTrue(self.sells(self.p))
        for o in self.sells(self.p):
            self.assertEqual(o["cashDate"], "2026-09-29")
            self.assertFalse(o["late"])
        self.assertEqual(self.p["lateSells"], [])
        self.assertEqual(self.approve().status_code, 200)

    def test_view_recalculates_after_market_close(self):
        self.clock.set(datetime(2026, 9, 23, 16, 0))                   # 장 마감 후
        p = self.pending()
        for o in self.sells(p):
            self.assertEqual(o["execDate"], "2026-09-28")              # 연휴 뒤 월요일 매도
            self.assertEqual(o["cashDate"], "2026-09-30")
            self.assertTrue(o["late"])
        self.assertTrue(p["lateSells"])

    def test_late_sell_needs_confirmation(self):
        self.clock.set(datetime(2026, 9, 23, 16, 0))
        r = self.approve()
        self.assertEqual(r.status_code, 409)
        j = r.get_json()
        self.assertTrue(j["needsAck"])
        self.assertEqual(j["lateSells"][0]["cashDate"], "2026-09-30")
        self.assertEqual(j["lateSells"][0]["dueDate"], "2026-09-29")
        self.assertEqual(self.pending()["status"], "승인 대기")          # 아직 발주 안 됨

        r = self.approve(acceptLate=True)
        self.assertEqual(r.status_code, 200)
        events = [a["event"] for a in self.c.get("/api/security").get_json()["audit"]]
        self.assertIn("지출일 초과 매도 확인 요청", events)
        self.assertIn("지출일 초과 매도 확인 후 승인", events)

    def test_results_show_recalculated_dates(self):
        self.clock.set(datetime(2026, 9, 23, 16, 0))
        results = self.approve(acceptLate=True).get_json()["results"]
        self.assertFalse(any("09/23" in r for r in results))            # 제안 때 날짜가 남아 있지 않음


if __name__ == "__main__":
    unittest.main()
