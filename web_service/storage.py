"""
서비스 상태 저장소 (SQLite)

- 요청으로 상태가 바뀔 때마다 전체 상태를 스냅숏으로 저장하고, 서버를 다시 켜면 마지막 스냅숏을 불러옵니다.
- 스냅숏은 한 트랜잭션으로 기록되므로 저장 도중 서버가 꺼져도 직전 스냅숏이 그대로 남습니다.
- 최근 KEEP 개를 보관 → 문제가 생기면 이전 시점으로 되돌릴 수 있습니다 (load(snapshot_id=...)).
- 각 스냅숏은 HMAC-SHA256 서명: DB 파일이 바깥에서 바뀌면 불러오지 않고 멈춥니다.
- 증권사 토큰·공휴일 API 키·주문 PIN 은 저장하지 않고, 켤 때 환경 변수에서 다시 채웁니다.

구조 버전(SCHEMA)이 다른 스냅숏은 불러오지 않습니다. 코드 구조를 바꿔 예전 스냅숏과 맞지 않게 되면
SCHEMA 를 올리고, 필요하면 이전 버전 → 새 버전 변환 코드를 추가하세요.
"""
from __future__ import annotations

import hashlib
import hmac
import os
import pickle
import sqlite3
from datetime import datetime
from typing import Optional

SCHEMA = 1
KEEP = 20


class StorageError(RuntimeError):
    pass


class TamperedSnapshot(StorageError):
    pass


class IncompatibleSnapshot(StorageError):
    pass


def _load_key(db_path: str) -> bytes:
    """서명 키: PORTFOLIO_DB_KEY 환경 변수, 없으면 DB 옆 .db_key 파일 (처음 한 번 생성, 본인만 읽기)"""
    env = os.environ.get("PORTFOLIO_DB_KEY")
    if env:
        return hashlib.sha256(env.encode()).digest()
    key_path = os.path.join(os.path.dirname(os.path.abspath(db_path)), ".db_key")
    if not os.path.exists(key_path):
        fd = os.open(key_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(fd, "wb") as f:
            f.write(os.urandom(32))
    with open(key_path, "rb") as f:
        return f.read()


class Store:
    def __init__(self, path: str, key: Optional[bytes] = None):
        self.path = path
        d = os.path.dirname(os.path.abspath(path))
        os.makedirs(d, exist_ok=True)
        self.key = key or _load_key(path)
        with self._conn() as c:
            c.execute("""CREATE TABLE IF NOT EXISTS snapshots (
                             id INTEGER PRIMARY KEY AUTOINCREMENT,
                             saved_at TEXT NOT NULL,
                             schema INTEGER NOT NULL,
                             reason TEXT,
                             mac TEXT NOT NULL,
                             data BLOB NOT NULL)""")

    def _conn(self) -> sqlite3.Connection:
        c = sqlite3.connect(self.path, timeout=10)
        c.execute("PRAGMA journal_mode=WAL")
        c.execute("PRAGMA synchronous=FULL")
        return c

    def _mac(self, schema: int, data: bytes) -> str:
        return hmac.new(self.key, str(schema).encode() + b"|" + data, hashlib.sha256).hexdigest()

    # ── 저장·불러오기 ──
    def save(self, state: dict, reason: str = "", saved_at: Optional[datetime] = None) -> int:
        data = pickle.dumps(state, protocol=pickle.HIGHEST_PROTOCOL)
        with self._conn() as c:
            cur = c.execute("INSERT INTO snapshots (saved_at, schema, reason, mac, data) VALUES (?, ?, ?, ?, ?)",
                            ((saved_at or datetime.now()).isoformat(timespec="seconds"), SCHEMA, reason,
                             self._mac(SCHEMA, data), data))
            sid = cur.lastrowid
            c.execute("DELETE FROM snapshots WHERE id NOT IN (SELECT id FROM snapshots ORDER BY id DESC LIMIT ?)",
                      (KEEP,))
        return sid

    def load(self, snapshot_id: Optional[int] = None) -> Optional[dict]:
        """마지막(또는 지정한) 스냅숏 → 상태 dict. 저장된 것이 없으면 None"""
        with self._conn() as c:
            if snapshot_id is None:
                row = c.execute("SELECT id, schema, mac, data FROM snapshots ORDER BY id DESC LIMIT 1").fetchone()
            else:
                row = c.execute("SELECT id, schema, mac, data FROM snapshots WHERE id = ?", (snapshot_id,)).fetchone()
        if row is None:
            return None
        sid, schema, mac, data = row
        if not hmac.compare_digest(mac, self._mac(schema, data)):
            raise TamperedSnapshot(f"스냅숏 #{sid}의 서명이 맞지 않아요. DB 파일이 바뀌었거나 서명 키가 달라요.")
        if schema != SCHEMA:
            raise IncompatibleSnapshot(f"스냅숏 #{sid}은 구조 버전 {schema}이고 지금 프로그램은 {SCHEMA}이에요.")
        try:
            return pickle.loads(data)
        except Exception as e:                      # 클래스 이름·구조가 바뀐 경우
            raise IncompatibleSnapshot(f"스냅숏 #{sid}을 지금 코드로 읽을 수 없어요: {e}") from e

    def history(self, limit: int = KEEP) -> list:
        with self._conn() as c:
            return [{"id": i, "savedAt": t, "schema": s, "reason": r, "bytes": n} for i, t, s, r, n in c.execute(
                "SELECT id, saved_at, schema, reason, length(data) FROM snapshots ORDER BY id DESC LIMIT ?",
                (limit,))]
