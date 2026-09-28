"""
서버(Render 등)에서 실행할 때의 시작점

  gunicorn wsgi:app --workers 1 --threads 8 --bind 0.0.0.0:$PORT

- 작업 프로세스는 반드시 1개: 데이터를 메모리에 들고 있어서, 여러 개면 프로세스마다 데이터가 따로 놀아요.
  (동시에 여러 사람이 접속하는 건 --threads 로 처리)
- python app.py 로 켤 때만 시작되던 매일 07:00 스캔을 여기서 시작해요.
"""
import threading

from app import _scheduler, app  # noqa: F401  (gunicorn 이 app 을 가져감)

threading.Thread(target=_scheduler, name="daily-scan", daemon=True).start()
