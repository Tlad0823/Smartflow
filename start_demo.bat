@echo off
rem Demo launcher: double-click to start. Close this window to stop.
cd /d "%~dp0"
where py >nul 2>nul && (py -3 demo.py) || (python demo.py)
pause
