@echo off
:: Builds and runs FpcSmoke with Free Pascal, Win32 + Win64.
:: Set FPCEXE if fpc.exe is not on the PATH.
setlocal
if "%FPCEXE%"=="" set "FPCEXE=fpc"
cd /d "%~dp0"
set "SRC=%~dp0..\Source"
set "OUT=%~dp0fpc"
set RC=0
for %%T in ("win32 i386" "win64 x86_64") do call :one %%~T
echo.
if "%RC%"=="0" (echo RESULT: all targets passed) else (echo RESULT: FAILURES)
endlocal & exit /b %RC%

:one
echo === FPC %1 %2 ===
if not exist "%OUT%\%2" mkdir "%OUT%\%2"
"%FPCEXE%" -T%1 -P%2 -B -vew -Fu"%SRC%" -Fi"%SRC%" -FE"%OUT%\%2" -FU"%OUT%\%2" FpcSmoke.dpr
if errorlevel 1 (set RC=2& exit /b)
"%OUT%\%2\FpcSmoke.exe"
if errorlevel 1 set RC=1
exit /b
