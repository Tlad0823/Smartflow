"""
화면 스모크 테스트 (실제 브라우저) — Playwright 가 없으면 자동으로 건너뜀
  설치: pip install playwright && playwright install chromium
"""
import threading
import unittest
from datetime import date, datetime

from tests.helpers import EngineTestCase, fresh_client, web

try:
    from playwright.sync_api import sync_playwright
    from werkzeug.serving import WSGIRequestHandler, make_server

    class _Quiet(WSGIRequestHandler):
        def log(self, *args):
            pass
    HAVE_BROWSER = True
except ImportError:
    HAVE_BROWSER = False


@unittest.skipUnless(HAVE_BROWSER, "Playwright 미설치")
class UiSmoke(EngineTestCase):
    TODAY = date(2026, 12, 1)

    def setUp(self):
        super().setUp()
        fresh_client()
        self.server = make_server("127.0.0.1", 0, web.app, request_handler=_Quiet)
        self.url = f"http://127.0.0.1:{self.server.server_port}/"
        threading.Thread(target=self.server.serve_forever, daemon=True).start()
        try:
            self.pw = sync_playwright().start()
            self.browser = self.pw.chromium.launch()
        except Exception as e:                      # 브라우저 파일이 없는 환경
            self.server.shutdown()
            self.skipTest(f"브라우저 실행 불가: {e}")
        self.page = self.browser.new_page()
        self.page.clock.install(time=datetime(2026, 12, 1, 9, 0))      # 화면의 '오늘'도 서버와 맞춤
        self.errors = []
        self.page.on("pageerror", lambda e: self.errors.append(str(e)))
        self.page.goto(self.url)
        self.page.wait_for_load_state("networkidle")

    def tearDown(self):
        self.browser.close()
        self.pw.stop()
        self.server.shutdown()
        super().tearDown()

    def test_onboarding_tab_renders_all_inputs(self):
        self.page.click("#tab-profile")
        self.page.wait_for_timeout(500)
        self.assertGreaterEqual(self.page.eval_on_selector("#dg-type", "e => e.options.length"), 2)
        self.assertGreaterEqual(self.page.eval_on_selector("#dg-m", "e => e.options.length"), 1)
        groups = self.page.eval_on_selector_all("#dg-qs input[type=radio]",
                                                "els => new Set(els.map(e => e.name)).size")
        self.assertEqual(groups, 5)
        self.assertEqual(self.errors, [])

    def test_no_demo_banner_normally(self):
        self.assertFalse(self.page.is_visible("#demo-bar"))

    def test_demo_banner_in_demo_mode(self):
        prev, web.DEMO = web.DEMO, True
        try:
            self.page.reload()
            self.page.wait_for_load_state("networkidle")
            self.assertTrue(self.page.is_visible("#demo-bar"))
            self.assertIn("시연용 데모", self.page.inner_text("#demo-bar"))

            # 발표자 초기화: PIN 입력 → 방문자가 넣은 일정이 사라지고 처음 데모 상태로
            web.app.test_client().post("/api/events", json={"date": "2026-12-10", "name": "방문자 입력",
                                                            "amount": 1, "big": False})
            self.page.once("dialog", lambda d: d.accept("135790"))
            self.page.click("#demo-reset")
            self.page.wait_for_load_state("networkidle")
            self.page.wait_for_timeout(500)
            names = [e["name"] for e in web.app.test_client().get("/api/calendar?year=2026&month=12")
                     .get_json()["events"]]
            self.assertNotIn("방문자 입력", names)
            self.assertEqual(self.errors, [])
        finally:
            web.DEMO = prev

    def test_calendar_shows_market_closures(self):
        self.page.click("#tab-ledger")
        self.page.wait_for_timeout(500)
        text = self.page.inner_text("body")
        self.assertIn("휴장: KOR, US", text)          # 12/25
        self.assertIn("휴장: KOR", text)              # 12/31 연말 휴장일
        self.assertEqual(self.errors, [])


if __name__ == "__main__":
    unittest.main()


@unittest.skipUnless(HAVE_BROWSER, "Playwright 미설치")
class UiLateApproval(EngineTestCase):
    """매매 제안 탭: 지출일 초과 경고 → 확인 창 → 승인"""
    TODAY = date(2026, 9, 23)

    def setUp(self):
        super().setUp()
        self.clock.set(datetime(2026, 9, 23, 11, 0))
        c = fresh_client()
        web.STATE.guard.per_order = web.STATE.guard.daily = 100_000_000
        c.post("/api/events", json={"date": "2026-09-29", "name": "이사 잔금", "amount": 30_000_000, "big": True})
        c.post("/api/triggers/scan", json={"source": "manual"})
        self.clock.set(datetime(2026, 9, 23, 16, 0))                    # 장 마감 후 승인하러 옴
        self.server = make_server("127.0.0.1", 0, web.app, request_handler=_Quiet)
        threading.Thread(target=self.server.serve_forever, daemon=True).start()
        try:
            self.pw = sync_playwright().start()
            self.browser = self.pw.chromium.launch()
        except Exception as e:
            self.server.shutdown()
            self.skipTest(f"브라우저 실행 불가: {e}")
        self.page = self.browser.new_page()
        self.page.clock.install(time=datetime(2026, 9, 23, 16, 0))
        self.dialogs = []
        self.page.on("dialog", lambda d: (self.dialogs.append(d.message), d.accept()))
        self.page.goto(f"http://127.0.0.1:{self.server.server_port}/")
        self.page.wait_for_load_state("networkidle")

    def tearDown(self):
        self.browser.close()
        self.pw.stop()
        self.server.shutdown()
        super().tearDown()

    def test_warning_confirm_and_approve(self):
        self.page.click("#tab-proposals")
        self.page.wait_for_timeout(500)
        text = self.page.inner_text("#pr-list")
        self.assertIn("지출일까지 대금이 들어오지 않는 매도", text)
        self.assertIn("지출일 9/29(화) 초과", text)
        pin = self.page.query_selector("[data-pin]")
        if pin:
            pin.fill("135790")
        self.page.click('[data-act="approve"]')
        self.page.wait_for_timeout(800)
        self.assertTrue(self.dialogs and "그래도 승인할까요?" in self.dialogs[0])
        self.assertIn("승인 완료", self.page.inner_text("#pr-list"))
