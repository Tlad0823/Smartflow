"""웹 API 기본 동작 (서버 없이 Flask 테스트 클라이언트로 확인)"""
import unittest

from tests.helpers import EngineTestCase, fresh_client


class Endpoints(EngineTestCase):
    def setUp(self):
        super().setUp()
        self.c = fresh_client()

    def test_main_pages_respond(self):
        for url in ("/", "/api/summary", "/api/triggers", "/api/onboarding", "/api/security",
                    "/api/proposals", "/api/calendar?year=2026&month=9"):
            self.assertEqual(self.c.get(url).status_code, 200, url)

    def test_onboarding_payload_is_complete(self):
        """성향 진단 탭: 소득 유형·비상금 준비 기간·설문이 그려질 데이터가 있는지"""
        j = self.c.get("/api/onboarding").get_json()
        self.assertGreaterEqual(len(j["incomeTypes"]), 2)
        for t in j["incomeTypes"]:
            self.assertLessEqual(t["mMin"], t["mMax"])
        self.assertEqual(len(j["questions"]), 5)
        for key in ("income_type", "m_multiplier", "answers", "goals"):
            self.assertIn(key, j["current"])

    def test_calendar_has_market_events_and_tax_ratio(self):
        j = self.c.get("/api/calendar?year=2026&month=11").get_json()
        self.assertAlmostEqual(j["taxRatio"], 0.15)
        self.assertTrue(any(e["market"] == "US" and e["kind"] == "휴장" for e in j["market"]))
        self.assertTrue(j["marketSource"])

    def test_taxable_cannot_exceed_irregular(self):
        L = {"monthly_income": 4_000_000, "total_expense": 2_600_000, "essential_expense": 2_600_000,
             "irregular_income": 500_000, "irregular_taxable": 600_000}
        self.assertEqual(self.c.put("/api/ledger/2026-09", json=L).status_code, 400)

    def test_trigger_c_status_shows_both_counts(self):
        self.c.post("/api/events", json={"date": "2026-10-20", "name": "이사 잔금", "amount": 30_000_000, "big": True})
        C = self.c.get("/api/triggers").get_json()["status"]["C"]
        self.assertEqual((C["dday"], C["businessDays"], C["dueDate"]), (27, 15, "2026-10-20"))  # 추석·개천절 대체·한글날 제외


if __name__ == "__main__":
    unittest.main()
