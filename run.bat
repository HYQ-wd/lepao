@echo off
chcp 65001 >nul 2>nul
setlocal
title LePao Auto Run

REM ============================================================
REM  Just double-click this file. Nothing to edit.
REM  Only touch the two optional lines below if MuMu is installed
REM  somewhere unusual or you want a specific instance.
REM ============================================================

REM optional: MuMu install root (the folder that contains nx_main)
set "MUMU_HOME="
REM optional: instance index. empty = auto-detect the one with both apps
set "MUMU_INDEX="

REM ============================================================

cd /d "%~dp0"

REM ---------- find python ----------
set "PY="
if exist "%~dp0python\python.exe" set "PY=%~dp0python\python.exe"
if not defined PY (
  py -3 -c "import sys" >nul 2>nul && set "PY=py -3"
)
if not defined PY (
  python -c "import sys" >nul 2>nul && set "PY=python"
)
if not defined PY (
  echo.
  echo [ERROR] Python not found.
  echo         Install Python 3.8+ from https://www.python.org/downloads/
  echo         and tick "Add Python to PATH" during setup.
  echo.
  pause
  exit /b 1
)

if defined MUMU_HOME set "LEPAO_MUMU_HOME=%MUMU_HOME%"
if defined MUMU_INDEX set "LEPAO_INDEX=%MUMU_INDEX%"
set "PYTHONIOENCODING=utf-8"
set "PYTHONUTF8=1"

REM optional first argument (normally omitted):
REM   run.bat go     locate MuMu + find both apps + start route loop  [default]
REM   run.bat check  environment self-test only
REM   run.bat boot   boot the emulator only
REM   run.bat fl     start FakeLocation route simulation only
set "ACTION=%~1"
if "%ACTION%"=="" set "ACTION=go"

%PY% "lepao_auto.py" %ACTION%
set "RC=%ERRORLEVEL%"

echo.
pause
exit /b %RC%
