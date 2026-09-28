"""
시연용 실행기 — 내 PC에서 프로그램을 켜고, 다른 사람이 들어올 수 있는 임시 링크를 만듭니다.

  Windows : start_demo.bat 더블클릭          Mac : start_demo.command 더블클릭
  (또는 명령어로 python demo.py)

하는 일
  1. 프로그램을 '시연 모드'로 켬: 데모 데이터로 메모리에서만 동작 (저장해 둔 내 데이터는 열지도 덮어쓰지도 않음)
  2. 이번 시연에만 쓸 주문 PIN 을 새로 만듦 (코드에 적힌 기본 PIN 을 쓰지 않도록)
  3. Cloudflare 임시 터널로 https://xxxx.trycloudflare.com 링크를 만듦 (계정 불필요)
     → 새 주소가 인터넷에 퍼지는 데 시간이 걸리므로, 바깥에서 실제로 열리는 것을 확인한 뒤 '준비 완료'를 알림
  4. 이 창을 닫거나 Ctrl+C 를 누르면 프로그램과 링크가 함께 꺼짐 → 링크는 그 뒤로 열리지 않음

필요한 것: cloudflared (처음 한 번 설치)
  Windows : winget install --id Cloudflare.cloudflared
  Mac     : brew install cloudflared
cloudflared 가 없으면 내 PC에서만 볼 수 있는 모드로 켭니다.
"""
from __future__ import annotations

import json
import os
import re
import secrets
import shutil
import signal
import socket
import ssl
import subprocess
import sys
import threading
import time
import urllib.parse
import urllib.request
import webbrowser

HERE = os.path.dirname(os.path.abspath(__file__))
LOG_PATH = os.path.join(HERE, "demo_log.txt")
# 임시 터널 주소만 (cloudflared 오류 메시지에 나오는 api.trycloudflare.com/... 는 제외)
TUNNEL_URL = re.compile(r"https://(?!api\.)[a-z0-9-]+\.trycloudflare\.com(?![\w./-])")
READY_TIMEOUT = 30
TUNNEL_TIMEOUT = 60
PUBLIC_TIMEOUT = int(os.environ.get("DEMO_PUBLIC_TIMEOUT", "120"))   # 바깥 접속 확인 최대 대기(초)
CHECK_INTERVAL = 2
# DNS 조회: 내 PC의 주소록(DNS 캐시)을 거치지 않고 공개 DNS 서비스에 직접 물어봄
#   → 확인하는 동안 '그런 주소 없음' 답이 내 PC에 기억돼 오히려 접속이 늦어지는 일을 막음
DOH_ENDPOINTS = ("https://cloudflare-dns.com/dns-query", "https://dns.google/resolve")
FALLBACK_AFTER = 20      # 공개 DNS 서비스가 막힌 네트워크면, 이 시간 뒤부터 일반 방식으로 확인


def say(msg: str = "") -> None:
    print(msg, flush=True)


def check_packages() -> bool:
    missing = []
    for mod, pkg in (("flask", "flask"), ("cryptography", "cryptography")):
        try:
            __import__(mod)
        except ImportError:
            missing.append(pkg)
    if missing:
        say(f"[준비 필요] 필요한 파이썬 패키지가 없어요: {', '.join(missing)}")
        say(f"  이 폴더에서 다음 명령을 한 번 실행해 주세요:  {sys.executable} -m pip install -r requirements.txt")
        return False
    return True


def find_cloudflared() -> str | None:
    exe = os.environ.get("CLOUDFLARED") or shutil.which("cloudflared")
    if exe:
        return exe
    if os.name == "nt":                                  # winget 설치 직후 PATH 에 아직 없을 때
        for p in (os.path.expandvars(r"%LOCALAPPDATA%\Microsoft\WinGet\Links\cloudflared.exe"),
                  r"C:\Program Files (x86)\cloudflared\cloudflared.exe",
                  r"C:\Program Files\cloudflared\cloudflared.exe"):
            if os.path.exists(p):
                return p
    return None


def free_port(start: int = 5000) -> int:
    for port in range(start, start + 50):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            try:
                s.bind(("127.0.0.1", port))
                return port
            except OSError:
                continue
    raise RuntimeError("비어 있는 포트를 찾지 못했어요.")


def wait_until_ready(port: int, proc: subprocess.Popen) -> bool:
    deadline = time.time() + READY_TIMEOUT
    while time.time() < deadline:
        if proc.poll() is not None:
            return False
        try:
            with urllib.request.urlopen(f"http://127.0.0.1:{port}/api/demo", timeout=2) as r:
                return b'"demo":true' in r.read().replace(b" ", b"")
        except Exception:
            time.sleep(0.3)
    return False


def start_app(port: int, pin: str, log) -> subprocess.Popen:
    env = dict(os.environ, PORTFOLIO_DEMO="1", PORTFOLIO_DB="off", ORDER_PIN=pin, PORT=str(port),
               PYTHONIOENCODING="utf-8")
    env.pop("PORTFOLIO_TODAY", None)
    return subprocess.Popen([sys.executable, os.path.join(HERE, "app.py")], cwd=HERE, env=env,
                            stdout=log, stderr=subprocess.STDOUT)


def start_tunnel(exe: str, port: int, log) -> tuple:
    """cloudflared 임시 터널 → (프로세스, 링크 또는 None)"""
    proc = subprocess.Popen([exe, "tunnel", "--no-autoupdate", "--url", f"http://127.0.0.1:{port}"],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                            encoding="utf-8", errors="replace")
    found: list = []

    def reader():
        for line in proc.stdout:
            log.write("[tunnel] " + line)
            log.flush()
            m = TUNNEL_URL.search(line)
            if m and not found:
                found.append(m.group(0))

    threading.Thread(target=reader, daemon=True).start()
    deadline = time.time() + TUNNEL_TIMEOUT
    while time.time() < deadline and not found and proc.poll() is None:
        time.sleep(0.2)
    return proc, (found[0] if found else None)


# ── 공유 링크가 바깥에서 실제로 열리는지 확인 ─────────────────────────────
def parse_doh(data: dict) -> tuple:
    """공개 DNS 응답(JSON) → ('ok', [IP…]) / ('nxdomain', [])"""
    if data.get("Status") == 3:                          # 아직 주소록에 없음
        return "nxdomain", []
    ips = [a["data"] for a in data.get("Answer", []) if a.get("type") == 1]
    return ("ok", ips) if ips else ("nxdomain", [])


def doh_lookup(host: str, timeout: float = 5) -> tuple:
    """('ok', [IP…]) / ('nxdomain', []) / ('error', []) — 공개 DNS 서비스가 모두 막혀 있으면 error"""
    for ep in DOH_ENDPOINTS:
        try:
            req = urllib.request.Request(f"{ep}?name={urllib.parse.quote(host)}&type=A",
                                         headers={"accept": "application/dns-json"})
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return parse_doh(json.loads(r.read()))
        except Exception:
            continue
    return "error", []


def probe_https(host: str, ip: str, path: str = "/api/demo", port: int = 443, timeout: float = 8,
                context: ssl.SSLContext | None = None) -> tuple:
    """찾아낸 IP로 직접 접속해 HTTPS 요청 (인증서는 host 이름으로 정상 검증) → (상태 코드, 본문)"""
    ctx = context or ssl.create_default_context()
    with socket.create_connection((ip, port), timeout=timeout) as raw:
        with ctx.wrap_socket(raw, server_hostname=host) as s:
            s.sendall((f"GET {path} HTTP/1.1\r\nHost: {host}\r\nAccept: application/json\r\n"
                       "User-Agent: portfolio-demo-check\r\nConnection: close\r\n\r\n").encode())
            buf = b""
            while len(buf) < 1_000_000:
                chunk = s.recv(65536)
                if not chunk:
                    break
                buf += chunk
    head, _, body = buf.partition(b"\r\n\r\n")
    return int(head.split(b" ", 2)[1]), body


def is_our_app(status: int, body: bytes) -> bool:
    """Cloudflare 오류 페이지(502·530 등)가 아니라 이 프로그램의 시연 모드 응답인지"""
    return status == 200 and b'"demo":true' in body.replace(b" ", b"")


def probe_system(url: str, timeout: float = 8) -> bool:
    """공개 DNS 서비스를 쓸 수 없을 때: 일반 방식(내 PC 주소록)으로 확인"""
    try:
        with urllib.request.urlopen(url.rstrip("/") + "/api/demo", timeout=timeout) as r:
            return is_our_app(r.status, r.read())
    except Exception:
        return False


def wait_until_public(url: str, tunnel: subprocess.Popen, timeout: float = PUBLIC_TIMEOUT, *,
                      lookup=doh_lookup, probe=probe_https, system_probe=probe_system,
                      sleep=time.sleep, clock=time.monotonic, on_progress=None) -> str:
    """
    공유 링크가 인터넷 어디서나 열릴 때까지 기다림
      1. 공개 DNS 에 새 주소가 등록됐는지 확인 (내 PC 주소록을 거치지 않음)
      2. 찾은 IP로 직접 접속해 이 프로그램이 응답하는지 확인
    반환: 'ready' / 'timeout' / 'tunnel_down'
    """
    host = urllib.parse.urlparse(url).hostname
    start = clock()
    while clock() - start < timeout:
        if tunnel is not None and tunnel.poll() is not None:
            return "tunnel_down"
        state, ips = lookup(host)
        if state == "ok":
            for ip in ips[:2]:
                try:
                    if is_our_app(*probe(host, ip)):
                        return "ready"
                except Exception:
                    pass
        elif state == "error" and clock() - start >= FALLBACK_AFTER:
            if system_probe(url):
                return "ready"
        if on_progress:
            on_progress(clock() - start)
        sleep(CHECK_INTERVAL)
    return "timeout"


def copy_to_clipboard(text: str) -> bool:
    try:
        if os.name == "nt":
            subprocess.run("clip", input=text.encode("utf-16le"), check=True, shell=True)
            return True
        if sys.platform == "darwin":
            subprocess.run(["pbcopy"], input=text.encode(), check=True)
            return True
    except Exception:
        pass
    return False


def stop(*procs) -> None:
    for p in procs:
        if p is not None and p.poll() is None:
            p.terminate()
    for p in procs:
        if p is not None:
            try:
                p.wait(timeout=5)
            except subprocess.TimeoutExpired:
                p.kill()
            if p.stdout is not None:
                p.stdout.close()


def _stop_on_signal(signum, frame):
    raise KeyboardInterrupt


def install_signal_handlers() -> None:
    """창 닫기·종료 신호도 Ctrl+C 처럼 처리 → 프로그램과 링크를 함께 정리"""
    for name in ("SIGINT", "SIGTERM", "SIGHUP", "SIGBREAK"):
        sig = getattr(signal, name, None)
        if sig is not None:
            try:
                signal.signal(sig, _stop_on_signal)
            except (ValueError, OSError):
                pass


def main() -> int:
    install_signal_handlers()
    say("=" * 64)
    say("  가계부 연동 자산관리 — 시연용 실행기")
    say("=" * 64)
    if not check_packages():
        return 1

    pin = os.environ.get("ORDER_PIN") or f"{secrets.randbelow(10**6):06d}"
    port = free_port()
    log = open(LOG_PATH, "w", encoding="utf-8")
    app_proc = tunnel = None
    try:
        say("프로그램을 시연 모드로 켜는 중…")
        app_proc = start_app(port, pin, log)
        if not wait_until_ready(port, app_proc):
            say(f"[실패] 프로그램이 켜지지 않았어요. 자세한 내용: {LOG_PATH}")
            return 1
        local = f"http://127.0.0.1:{port}/"

        exe = find_cloudflared()
        url = None
        if exe is None:
            say()
            say("[안내] cloudflared 가 설치돼 있지 않아서 공유 링크를 만들 수 없어요.")
            say("  Windows : winget install --id Cloudflare.cloudflared")
            say("  Mac     : brew install cloudflared")
            say("  설치 후 이 실행기를 다시 켜면 링크가 만들어져요. 지금은 내 PC에서만 볼 수 있어요.")
        else:
            say("다른 사람이 들어올 수 있는 임시 링크를 만드는 중… (최대 1분)")
            tunnel, url = start_tunnel(exe, port, log)
            if url is None:
                say(f"[실패] 링크를 만들지 못했어요. 인터넷 연결을 확인해 주세요. 자세한 내용: {LOG_PATH}")
                say("  지금은 내 PC에서만 볼 수 있어요.")
                stop(tunnel)
                tunnel = None

        public = None
        if url:
            say("링크가 만들어졌어요. 바깥에서 실제로 열리는지 확인하는 중… (보통 10~30초)")

            def progress(sec: float) -> None:
                print(f"\r  확인 중… {int(sec)}초", end="", flush=True)

            public = wait_until_public(url, tunnel, on_progress=progress)
            print("\r" + " " * 30 + "\r", end="", flush=True)
            log.write(f"[check] public={public}\n")
            log.flush()
            if public == "tunnel_down":
                say(f"[중단] 링크 연결이 끊겼어요. 실행기를 다시 켜 주세요. 자세한 내용: {LOG_PATH}")
                return 1

        say()
        say("-" * 64)
        if url and public == "ready":
            say("  ✔ 준비 완료 — 바깥에서 접속되는 것을 확인했어요.")
            say(f"  공유 링크   {url}")
            if copy_to_clipboard(url):
                say("              (클립보드에 복사했어요 — 메신저에 붙여 넣으면 돼요)")
        elif url:
            say(f"  공유 링크   {url}")
            say(f"  ⚠ {PUBLIC_TIMEOUT}초 동안 바깥 접속을 확인하지 못했어요. 1~2분 뒤 한 번 열어 보고, 열리면 보내 주세요.")
            say("    (학교·회사 네트워크가 확인을 막는 경우도 있어요. 링크 자체는 살아 있어요.)")
        say(f"  내 PC에서   {local}")
        say(f"  주문 PIN    {pin}   ← 발표자만 알고 있기 (승인·'처음 상태로 되돌리기'에 필요)")
        say("-" * 64)
        if url:
            say("  · 링크를 받은 사람은 설치 없이 브라우저로 바로 들어와요.")
            say("  · 모두 같은 데모 데이터를 함께 써요. 끝나면 데이터는 사라져요.")
            say("  · 시연을 끝내려면 이 창을 닫거나 Ctrl+C 를 누르세요. 링크도 함께 닫혀요.")
        else:
            say("  · 데모 데이터로 동작하고, 끝나면 데이터는 사라져요.")
            say("  · 끝내려면 이 창을 닫거나 Ctrl+C 를 누르세요.")
        say("-" * 64)
        # 확인이 끝난 경우에만 공유 링크로 열기 — 준비 전에 열면 '없는 주소'가 내 PC에 기억될 수 있음
        webbrowser.open(url if public == "ready" else local)

        while True:
            time.sleep(1)
            if app_proc.poll() is not None:
                say(f"[중단] 프로그램이 멈췄어요. 자세한 내용: {LOG_PATH}")
                return 1
            if tunnel is not None and tunnel.poll() is not None:
                say("[중단] 공유 링크 연결이 끊겼어요. 실행기를 다시 켜면 새 링크가 만들어져요.")
                return 1
    except KeyboardInterrupt:
        say()
        say("시연을 끝내는 중…")
        return 0
    finally:
        stop(tunnel, app_proc)
        log.close()
        say("프로그램과 공유 링크를 모두 닫았어요.")


if __name__ == "__main__":
    sys.exit(main())
