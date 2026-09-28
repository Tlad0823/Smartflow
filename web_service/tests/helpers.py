"""
테스트 공통 도구
  - 시계를 고정(FixedClock)해서 실행 날짜와 무관하게 같은 결과가 나오게 함
  - 공휴일 API 키·모의 날짜 환경 변수는 무시 (내장 예비 데이터로만 계산 → 네트워크 불필요)
"""
import copy
import os
import sys
import unittest
import warnings
from datetime import date

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)
os.environ.pop("HOLIDAY_API_KEY", None)
os.environ.pop("PORTFOLIO_TODAY", None)
os.environ["ORDER_PIN"] = "135790"            # 테스트용 PIN (시연 모드의 무작위 PIN 대신 고정값)
os.environ["PORTFOLIO_DB"] = "off"            # 테스트는 실제 DB를 건드리지 않음 (저장 테스트는 임시 파일 사용)
warnings.filterwarnings("ignore")

import portfolio_engine as pe  # noqa: E402
import app as web              # noqa: E402

ESSENTIAL = 2_600_000


def income_for(buffer_pct: float) -> float:
    """Buffer(%) 가 되도록 하는 월 소득 (필수 지출 고정)"""
    return ESSENTIAL / (1 - buffer_pct / 100)


class EngineTestCase(unittest.TestCase):
    """각 테스트마다 시계를 TODAY 로 고정하고, 끝나면 원래 시계로 되돌림"""
    TODAY = date(2026, 9, 23)

    def setUp(self):
        self.clock = pe.FixedClock(self.TODAY)
        self._prev_clock = pe.set_clock(self.clock)

    def tearDown(self):
        pe.set_clock(self._prev_clock)

    @staticmethod
    def manager():
        """데모 사용자 상태의 독립 복사본"""
        return copy.deepcopy(web.STATE.manager)


class MonthRunner:
    """
    월 마감을 차례로 돌리는 도우미 (2027-01부터 한 달씩)
      close(buf=, bal=, up=, dday=) → 판단 기록(log)
    """

    def __init__(self, manager, start_year: int = 2027):
        self.m, self.n, self.year = manager, 0, start_year
        self.reserve = manager.c_reserve(ESSENTIAL)

    def snap(self, buf=35, bal=None, up=0, dday=None, bdays=None, due=None):
        self.n += 1
        y, mo = self.year + (self.n - 1) // 12, (self.n - 1) % 12 + 1
        return pe.LedgerSnapshot(income_for(buf), ESSENTIAL,
                                 emergency_balance=self.reserve * 1.5 if bal is None else bal,
                                 upcoming_cf=up, dday=dday, bdays=bdays, due_date=due,
                                 period=f"{y}-{mo:02d}", total_expense=ESSENTIAL)

    def close(self, **kw):
        log, _ = self.m.monthly_cycle(self.snap(**kw))
        return log

    def state(self, key):
        latch = self.m.latches[key]
        return latch.active, latch.level


def has(log, *words):
    """로그 중 words 를 모두 포함한 줄이 있는지"""
    return any(all(w in line for w in words) for line in log)


def fresh_client():
    """웹 서비스 상태를 초기화한 테스트 클라이언트"""
    web.STATE = web.ServiceState(pe.clock_today())
    return web.app.test_client()
