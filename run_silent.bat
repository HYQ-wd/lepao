@echo off
chcp 65001 >nul 2>nul
setlocal
title LePao Auto Run (silent)

REM silent version: no window, log goes to _probe\run.log
REM normal usage is run.bat; keep this for troubleshooting / task scheduler.

set "MUMU_HOME="
set "MUMU_INDEX="

cd /d "%~dp0"
if not exist "_probe" mkdir "_probe"

set "PY="
if exist "%~dp0python\python.exe" set "PY=%~dp0python\python.exe"
if not defined PY (
  py -3 -c "import sys" >nul 2>nul && set "PY=py -3"
)
if not defined PY (
  python -c "import sys" >nul 2>nul && set "PY=python"
)
if not defined PY exit /b 1

if defined MUMU_HOME set "LEPAO_MUMU_HOME=%MUMU_HOME%"
if defined MUMU_INDEX set "LEPAO_INDEX=%MUMU_INDEX%"
set "PYTHONIOENCODING=utf-8"
set "PYTHONUTF8=1"

set "ACTION=%~1"
if "%ACTION%"=="" set "ACTION=go"

%PY% "lepao_auto.py" %ACTION% > "_probe\run.log" 2>&1

exit /b %ERRORLEVEL%
