"""서버 배포(Render) 환경: UTC 서버에서도 한국 시간, 시연 모드 PIN, wsgi 시작점"""
import os
import subprocess
import sys
import unittest

from tests.helpers import ROOT


def run(code: str, **env) -> str:
    e = {k: v for k, v in os.environ.items() if k not in ("ORDER_PIN", "PORTFOLIO_TODAY")}
    e.update(env)
    out = subprocess.run([sys.executable, "-c", code], cwd=ROOT, env=e, capture_output=True, text=True, timeout=60)
    if out.returncode:
        raise AssertionError(out.stderr)
    return out.stdout.strip().splitlines()[-1]


class ServerEnvironment(unittest.TestCase):
    def test_utc_server_uses_korea_time(self):
        diff = run("import datetime as d, portfolio_engine as pe;"
                   "print(round((pe.clock_now() - d.datetime.utcnow()).total_seconds() / 3600))", TZ="UTC")
        self.assertEqual(diff, "9")

    def test_demo_without_pin_never_uses_default(self):
        code = ("import app; ok, _ = app.STATE.pin.verify('135790'); "
                "print(ok, app._GENERATED_PIN is not None and len(app._GENERATED_PIN) == 6)")
        self.assertEqual(run(code, PORTFOLIO_DEMO="1", PORTFOLIO_DB="off"), "False True")

    def test_pin_from_environment(self):
        code = "import app; print(app.STATE.pin.verify('482913')[0])"
        self.assertEqual(run(code, PORTFOLIO_DEMO="1", PORTFOLIO_DB="off", ORDER_PIN="482913"), "True")

    def test_wsgi_starts_daily_scan(self):
        code = "import threading, wsgi; print(any(t.name == 'daily-scan' for t in threading.enumerate()))"
        self.assertEqual(run(code, PORTFOLIO_DEMO="1", PORTFOLIO_DB="off", ORDER_PIN="482913"), "True")

    def test_render_blueprint(self):
        with open(os.path.join(ROOT, "render.yaml"), encoding="utf-8") as f:
            text = f.read()
        for must in ("plan: free", "wsgi:app", "--workers 1", "0.0.0.0:$PORT", "PORTFOLIO_DEMO",
                     'value: "1"', "ORDER_PIN", "sync: false", "Asia/Seoul"):
            self.assertIn(must, text)
        self.assertNotRegex(text, r"ORDER_PIN\s*\n\s*value:")              # PIN 값을 파일에 적지 않음


if __name__ == "__main__":
    unittest.main()
