@echo off
:: DDetours test suite (DUnitX), Win32 + Win64.
::   build_test.bat          normal path
::   build_test.bat force    force the absolute branch (DDETOURS_FORCE_ABSRIP),
::                           which relocation only takes when the trampoline
::                           lands further than 2 GB away. Both runs must pass.
setlocal

:: ---------------------------------------------------------------------------
:: Delphi installation. Either edit the line below, or set DELPHIROOT in the
:: environment before calling. A default install is something like
::   C:\Program Files (x86)\Embarcadero\Studio\23.0
:: and is picked up automatically via %BDS% when this path does not exist.
:: ---------------------------------------------------------------------------
if "%DELPHIROOT%"=="" set "DELPHIROOT=C:\Delphi\12.3"
if not exist "%DELPHIROOT%\bin\rsvars.bat" if defined BDS set "DELPHIROOT=%BDS%"
if not exist "%DELPHIROOT%\bin\rsvars.bat" (
  echo rsvars.bat not found under "%DELPHIROOT%".
  echo Set DELPHIROOT to your Delphi installation folder and try again.
  exit /b 1
)

call "%DELPHIROOT%\bin\rsvars.bat" >nul
cd /d "%~dp0"

set "LIB32=%DELPHIROOT%\lib\win32\release"
set "LIB64=%DELPHIROOT%\lib\win64\release"
set "SRC=%~dp0..\Source"
set "NS=System;System.Win;Winapi"

:: -DCI keeps the DUnitX console runner from waiting for a key press.
set DEF=-DCI
if /I "%~1"=="force" set DEF=-DCI -DDDETOURS_FORCE_ABSRIP

echo === Test suite Win32 %DEF% ===
dcc32 -B -Q %DEF% -U"%LIB32%;%SRC%" -NS"%NS%" -N"%~dp0." -E"%~dp0." -TX.x86.exe Test.dpr
if errorlevel 1 goto :buildfailed
echo === Test suite Win64 %DEF% ===
dcc64 -B -Q %DEF% -U"%LIB64%;%SRC%" -NS"%NS%" -N"%~dp0." -E"%~dp0." -TX.x64.exe Test.dpr
if errorlevel 1 goto :buildfailed

:: DecodeProbe is a diagnostic tool, not part of the suite - built, not run.
:: Run it by hand when a hook corrupts its target: it shows what the decoder
:: makes of an instruction (a wrong length is the usual culprit).
echo === DecodeProbe (diagnostic, not executed) ===
dcc32 -B -Q -U"%LIB32%;%SRC%" -NS"%NS%" -N"%~dp0." -TX.x86.exe DecodeProbe.dpr
dcc64 -B -Q -U"%LIB64%;%SRC%" -NS"%NS%" -N"%~dp0." -TX.x64.exe DecodeProbe.dpr

del /q *.dcu 2>nul

set RC=0
echo.
echo --- run Win32 ---
"%~dp0Test.x86.exe"
if errorlevel 1 set RC=1
echo --- run Win64 ---
"%~dp0Test.x64.exe"
if errorlevel 1 set RC=1
echo.
if "%RC%"=="0" (echo RESULT: all tests passed) else (echo RESULT: FAILURES)
endlocal & exit /b %RC%

:buildfailed
echo BUILD FAILED
endlocal & exit /b 2
