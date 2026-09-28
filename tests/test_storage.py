"""DB 저장: 서버를 다시 켜도 데이터가 남는지, 비밀값이 저장되지 않는지, 변조·구조 변경 감지"""
import os
import sqlite3
import tempfile
import unittest
from datetime import date

from tests.helpers import EngineTestCase, fresh_client, web

import storage


class StoreBasics(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.path = os.path.join(self.dir.name, "t.db")
        self.store = storage.Store(self.path, key=b"k" * 32)

    def tearDown(self):
        self.dir.cleanup()

    def test_round_trip_and_empty(self):
        self.assertIsNone(self.store.load())
        self.store.save({"a": 1, "d": date(2026, 9, 23)}, "first")
        self.assertEqual(self.store.load(), {"a": 1, "d": date(2026, 9, 23)})

    def test_keeps_recent_snapshots_only(self):
        for i in range(storage.KEEP + 5):
            self.store.save({"n": i})
        hist = self.store.history(100)
        self.assertEqual(len(hist), storage.KEEP)
        self.assertEqual(self.store.load(), {"n": storage.KEEP + 4})
        self.assertEqual(self.store.load(snapshot_id=hist[-1]["id"]), {"n": 5})     # 이전 시점으로 되돌리기

    def test_tampered_snapshot_is_refused(self):
        self.store.save({"a": 1})
        with sqlite3.connect(self.path) as c:
            c.execute("UPDATE snapshots SET data = ?", (b"\x80\x04K\x02.",))
        with self.assertRaises(storage.TamperedSnapshot):
            self.store.load()

    def test_wrong_key_is_refused(self):
        self.store.save({"a": 1})
        with self.assertRaises(storage.TamperedSnapshot):
            storage.Store(self.path, key=b"x" * 32).load()

    def test_other_schema_is_refused(self):
        old = storage.SCHEMA
        storage.SCHEMA = old + 1
        try:
            self.store.save({"a": 1})
        finally:
            storage.SCHEMA = old
        with self.assertRaises(storage.IncompatibleSnapshot):
            self.store.load()

    def test_key_file_created_private(self):
        s = storage.Store(os.path.join(self.dir.name, "k.db"))
        key_file = os.path.join(self.dir.name, ".db_key")
        self.assertTrue(os.path.exists(key_file))
        if os.name == "posix":
            self.assertEqual(os.stat(key_file).st_mode & 0o777, 0o600)
        self.assertEqual(len(s.key), 32)


class ServiceRestart(EngineTestCase):
    """웹 서비스: 요청마다 저장 → '재시작'(DB에서 새로 불러오기) 후에도 그대로"""

    def setUp(self):
        super().setUp()
        self.dir = tempfile.TemporaryDirectory()
        self.path = os.path.join(self.dir.name, "svc.db")
        self._prev_store = web.STORE
        web.STORE = storage.Store(self.path, key=b"s" * 32)
        self.c = fresh_client()

    def tearDown(self):
        web.STORE = self._prev_store
        self.dir.cleanup()
        super().tearDown()

    def restart(self):
        web.STATE = web.ServiceState.restore(web.STORE.load())
        return web.app.test_client()

    def test_data_survives_restart(self):
        self.c.post("/api/events", json={"date": "2026-10-20", "name": "이사 잔금", "amount": 30_000_000, "big": True})
        L = {"monthly_income": 4_000_000, "total_expense": 2_600_000, "essential_expense": 2_600_000,
             "emergency_balance": 12_000_000}
        self.c.put("/api/ledger/2026-09", json=L)
        self.c.post("/api/ledger/2026-09/close")
        before_ids = web.STATE.last_id
        before_proposals = len(self.c.get("/api/proposals").get_json())
        before_latches = {k: (v.active, v.level) for k, v in web.STATE.manager.latches.items()}

        c2 = self.restart()
        self.assertIn("이사 잔금", [e["name"] for e in c2.get("/api/calendar?year=2026&month=10").get_json()["events"]])
        self.assertEqual(web.STATE.ledgers["2026-09"]["emergency_balance"], 12_000_000)
        self.assertEqual(len(c2.get("/api/proposals").get_json()), before_proposals)
        self.assertEqual({k: (v.active, v.level) for k, v in web.STATE.manager.latches.items()}, before_latches)
        eid = c2.post("/api/events", json={"date": "2026-10-21", "name": "x", "amount": 1, "big": False}).get_json()["id"]
        self.assertGreater(eid, before_ids)                           # 번호가 이어짐 (겹치지 않음)
        self.assertTrue(c2.get("/api/security").get_json()["auditValid"])

    def test_secrets_are_not_stored(self):
        class FakeProvider:
            key = "HOLIDAY-SECRET-123"
        web.STATE.calendar.provider = FakeProvider()
        web.save_state("test")
        with sqlite3.connect(self.path) as c:
            blob = c.execute("SELECT data FROM snapshots ORDER BY id DESC LIMIT 1").fetchone()[0]
        for secret in (b"demo-trade", b"demo-read", b"HOLIDAY-SECRET-123"):
            self.assertNotIn(secret, blob)
        c2 = self.restart()
        self.assertTrue(web.STATE.broker.can_trade)                  # 켤 때 환경 변수로 다시 연결
        self.assertEqual(c2.get("/api/summary").status_code, 200)

    def test_pin_lock_survives_restart(self):
        web.STATE.pin.failures = 3
        web.save_state("test")
        self.restart()
        self.assertEqual(web.STATE.pin.failures, 3)

    def test_storage_status_endpoint(self):
        self.c.post("/api/events", json={"date": "2026-10-21", "name": "x", "amount": 1, "big": False})
        st = self.c.get("/api/storage").get_json()
        self.assertIsNone(st["error"])
        self.assertTrue(st["history"])


if __name__ == "__main__":
    unittest.main()
