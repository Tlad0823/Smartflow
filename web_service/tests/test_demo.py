"""시연 모드: 내 저장 데이터를 건드리지 않는지, 발표자 초기화, 실행기 도우미"""
import os
import subprocess
import sys
import tempfile
import textwrap
import unittest

from tests.helpers import ROOT, EngineTestCase, fresh_client, web

import demo


class DemoNeverTouchesRealData(unittest.TestCase):
    def test_demo_mode_ignores_db_path(self):
        with tempfile.TemporaryDirectory() as d:
            db = os.path.join(d, "real.db")
            code = textwrap.dedent("""
                import app
                c = app.app.test_client()
                c.post('/api/events', json={'date': '2026-10-20', 'name': 'x', 'amount': 1, 'big': False})
                print(app.STORE is None, c.get('/api/storage').get_json()['path'])
            """)
            env = dict(os.environ, PORTFOLIO_DEMO="1", PORTFOLIO_DB=db)
            out = subprocess.run([sys.executable, "-c", code], cwd=ROOT, env=env,
                                 capture_output=True, text=True, timeout=60)
            self.assertEqual(out.stdout.strip().splitlines()[-1], "True None", out.stderr)
            self.assertFalse(os.path.exists(db))                      # DB 파일을 만들지도 않음


class DemoReset(EngineTestCase):
    def setUp(self):
        super().setUp()
        self._demo = web.DEMO
        web.DEMO = True
        self.c = fresh_client()

    def tearDown(self):
        web.DEMO = self._demo
        super().tearDown()

    def names(self):
        return [e["name"] for e in self.c.get("/api/calendar?year=2026&month=10").get_json()["events"]]

    def test_status(self):
        self.assertTrue(self.c.get("/api/demo").get_json()["demo"])

    def test_wrong_pin_rejected(self):
        self.c.post("/api/events", json={"date": "2026-10-20", "name": "방문자 입력", "amount": 1, "big": False})
        self.assertEqual(self.c.post("/api/demo/reset", json={"pin": "000000"}).status_code, 401)
        self.assertIn("방문자 입력", self.names())

    def test_reset_restores_demo_data(self):
        self.c.post("/api/events", json={"date": "2026-10-20", "name": "방문자 입력", "amount": 1, "big": False})
        self.assertEqual(self.c.post("/api/demo/reset", json={"pin": "135790"}).status_code, 200)
        self.assertNotIn("방문자 입력", self.names())
        self.assertIn("추석 연휴 가족 여행 잔금", self.names())         # 처음 데모 데이터
        self.assertEqual(web.MONITOR["history"], [])

    def test_reset_unavailable_outside_demo(self):
        web.DEMO = False
        self.assertEqual(self.c.post("/api/demo/reset", json={"pin": "135790"}).status_code, 404)


class LauncherHelpers(unittest.TestCase):
    def test_tunnel_url_pattern(self):
        line = "INF |  https://brave-ocean-sample-demo.trycloudflare.com                  |"
        self.assertEqual(demo.TUNNEL_URL.search(line).group(0), "https://brave-ocean-sample-demo.trycloudflare.com")
        # cloudflared 오류 메시지 속 API 주소를 링크로 착각하면 안 됨
        self.assertIsNone(demo.TUNNEL_URL.search('failed to request quick Tunnel: Post "https://api.trycloudflare.com/tunnel"'))
        self.assertIsNone(demo.TUNNEL_URL.search("https://abc.trycloudflare.com.evil.example"))

    def test_free_port(self):
        self.assertTrue(5000 <= demo.free_port() < 5050)

    @unittest.skipIf(os.name == "nt", "가짜 cloudflared 스크립트는 macOS/Linux 에서만")
    def test_start_tunnel_reads_link(self):
        with tempfile.TemporaryDirectory() as d:
            fake = os.path.join(d, "cloudflared")
            with open(fake, "w") as f:
                f.write("#!/bin/sh\necho 'INF Requesting new quick Tunnel'\n"
                        "echo 'INF |  https://abc-def.trycloudflare.com  |'\nexec sleep 30\n")
            os.chmod(fake, 0o755)
            with open(os.path.join(d, "log.txt"), "w") as log:
                proc, url = demo.start_tunnel(fake, 5000, log)
                demo.stop(proc)
            self.assertEqual(url, "https://abc-def.trycloudflare.com")
            self.assertIsNotNone(proc.poll())


if __name__ == "__main__":
    unittest.main()


class FakeClock:
    def __init__(self):
        self.t = 0.0

    def __call__(self):
        return self.t

    def sleep(self, sec):
        self.t += sec


class AliveTunnel:
    def __init__(self, dies_at=None, clock=None):
        self.dies_at, self.clock = dies_at, clock

    def poll(self):
        return 1 if self.dies_at is not None and self.clock() >= self.dies_at else None


URL = "https://brave-ocean-sample-demo.trycloudflare.com"
OK_BODY = b'{"demo":true}\n'


class PublicReadiness(unittest.TestCase):
    """링크를 알리기 전에 바깥에서 실제로 열리는지 확인"""

    def test_parse_doh(self):
        self.assertEqual(demo.parse_doh({"Status": 3}), ("nxdomain", []))
        self.assertEqual(demo.parse_doh({"Status": 0, "Answer": [{"type": 1, "data": "104.16.1.1"}]}),
                         ("ok", ["104.16.1.1"]))
        self.assertEqual(demo.parse_doh({"Status": 0, "Answer": [{"type": 5, "data": "x.example."}]}),
                         ("nxdomain", []))

    def test_is_our_app(self):
        self.assertTrue(demo.is_our_app(200, b'{"demo": true}'))
        self.assertFalse(demo.is_our_app(530, b"error 1033"))                # 터널 연결 전 Cloudflare 오류
        self.assertFalse(demo.is_our_app(200, b"<html>other</html>"))

    def test_waits_for_dns_then_app(self):
        clk = FakeClock()
        answers = iter([("nxdomain", [])] * 3 + [("ok", ["104.16.1.1"])] * 10)
        probes = iter([(530, b"1033"), (200, OK_BODY)])
        calls = []

        def probe(host, ip):
            calls.append((host, ip))
            return next(probes)

        r = demo.wait_until_public(URL, AliveTunnel(), 120, lookup=lambda h: next(answers), probe=probe,
                                   system_probe=lambda u: self.fail("공개 DNS 가 되면 일반 방식은 안 씀"),
                                   sleep=clk.sleep, clock=clk)
        self.assertEqual(r, "ready")
        self.assertEqual(calls, [("brave-ocean-sample-demo.trycloudflare.com", "104.16.1.1")] * 2)
        self.assertEqual(clk.t, 8)                                             # 확인 4번 × 2초

    def test_timeout_when_never_ready(self):
        clk = FakeClock()
        r = demo.wait_until_public(URL, AliveTunnel(), 30, lookup=lambda h: ("nxdomain", []),
                                   sleep=clk.sleep, clock=clk)
        self.assertEqual(r, "timeout")

    def test_tunnel_down(self):
        clk = FakeClock()
        r = demo.wait_until_public(URL, AliveTunnel(dies_at=6, clock=clk), 60, lookup=lambda h: ("nxdomain", []),
                                   sleep=clk.sleep, clock=clk)
        self.assertEqual(r, "tunnel_down")

    def test_fallback_when_public_dns_blocked(self):
        clk = FakeClock()
        seen = []

        def system_probe(url):
            seen.append(clk())
            return True

        r = demo.wait_until_public(URL, AliveTunnel(), 120, lookup=lambda h: ("error", []),
                                   system_probe=system_probe, sleep=clk.sleep, clock=clk)
        self.assertEqual(r, "ready")
        self.assertGreaterEqual(seen[0], demo.FALLBACK_AFTER)                  # 바로 묻지 않고 기다렸다가


class ProbeHttpsTls(unittest.TestCase):
    """찾아낸 IP로 직접 접속하면서도 인증서는 링크 주소 이름으로 검증되는지 (실제 TLS)"""
    HOST = "abc-def.trycloudflare.com"

    def setUp(self):
        import datetime as dt
        import ssl
        import threading
        from cryptography import x509
        from cryptography.hazmat.primitives import hashes, serialization
        from cryptography.hazmat.primitives.asymmetric import ec
        from cryptography.x509.oid import NameOID

        self.dir = tempfile.TemporaryDirectory()
        key = ec.generate_private_key(ec.SECP256R1())
        name = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, self.HOST)])
        now = dt.datetime.now(dt.timezone.utc)
        cert = (x509.CertificateBuilder().subject_name(name).issuer_name(name).public_key(key.public_key())
                .serial_number(x509.random_serial_number()).not_valid_before(now - dt.timedelta(minutes=1))
                .not_valid_after(now + dt.timedelta(hours=1))
                .add_extension(x509.SubjectAlternativeName([x509.DNSName(self.HOST)]), critical=False)
                .sign(key, hashes.SHA256()))
        self.cert = os.path.join(self.dir.name, "c.pem")
        keyf = os.path.join(self.dir.name, "k.pem")
        with open(self.cert, "wb") as f:
            f.write(cert.public_bytes(serialization.Encoding.PEM))
        with open(keyf, "wb") as f:
            f.write(key.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8,
                                      serialization.NoEncryption()))
        sctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        sctx.load_cert_chain(self.cert, keyf)
        import socket
        self.lsock = socket.socket()
        self.lsock.bind(("127.0.0.1", 0))
        self.lsock.listen(5)
        self.port = self.lsock.getsockname()[1]
        self.requests = []

        def serve():
            while True:
                try:
                    conn, _ = self.lsock.accept()
                except OSError:
                    return
                try:
                    with sctx.wrap_socket(conn, server_side=True) as s:
                        self.requests.append(s.recv(4096))
                        s.sendall(b"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 14\r\n"
                                  b"Connection: close\r\n\r\n" + OK_BODY)
                except Exception:
                    pass

        threading.Thread(target=serve, daemon=True).start()

    def tearDown(self):
        self.lsock.close()
        self.dir.cleanup()

    def client_ctx(self):
        import ssl
        ctx = ssl.create_default_context()
        ctx.load_verify_locations(self.cert)
        return ctx

    def test_direct_ip_with_host_name(self):
        status, body = demo.probe_https(self.HOST, "127.0.0.1", port=self.port, context=self.client_ctx())
        self.assertTrue(demo.is_our_app(status, body))
        self.assertIn(f"Host: {self.HOST}".encode(), self.requests[0])

    def test_wrong_name_is_rejected(self):
        import ssl
        with self.assertRaises(ssl.SSLCertVerificationError):
            demo.probe_https("someone-else.trycloudflare.com", "127.0.0.1", port=self.port,
                             context=self.client_ctx())
