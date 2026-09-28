"""나이·목표 시점: 남은 기간에 따른 투자 기간 점수와 목표별 비중"""
import unittest
from datetime import date

from tests.helpers import EngineTestCase, fresh_client, pe


class GoalGlidePath(EngineTestCase):
    def setUp(self):
        super().setUp()
        self.goals = pe.LifeGoals(1992, 60, (pe.Goal("주택 구입", 2031, 30, "home"),))

    def test_risky_share_falls_as_goal_nears(self):
        risky = []
        for y in (2026, 2028, 2030):
            t = pe.goal_blended_targets(5, self.goals, date(y, 1, 1))
            self.assertAlmostEqual(sum(t.values()), 100, places=2)
            risky.append(sum(v for k, v in t.items() if k in (pe.DOM_EQ, pe.FOR_EQ)))
        self.assertGreater(risky[0], risky[1])
        self.assertGreater(risky[1], risky[2])

    def test_passed_goal_is_flagged(self):
        self.assertIn("주택 구입", self.goals.passed(date(2032, 1, 1)))
        self.assertEqual(self.goals.passed(date(2030, 1, 1)), [])


class GoalInputValidation(EngineTestCase):
    def test_share_over_100_rejected(self):
        c = fresh_client()
        body = dict(c.get("/api/onboarding").get_json()["current"])
        body["goals"] = {"birth_year": "1992", "home_year": "2028", "home_share": "120"}
        self.assertEqual(c.post("/api/onboarding/evaluate", json=body).status_code, 400)

    def test_valid_goals_accepted(self):
        c = fresh_client()
        body = dict(c.get("/api/onboarding").get_json()["current"])
        body["goals"] = {"birth_year": "1992", "retirement_age": "60", "home_year": "2028", "home_share": "40"}
        self.assertEqual(c.post("/api/onboarding/evaluate", json=body).status_code, 200)


if __name__ == "__main__":
    unittest.main()
