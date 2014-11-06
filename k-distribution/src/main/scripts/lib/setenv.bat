@ECHO off
for /f "delims=" %%i in ('java -version 2^>^&1') do set VERSION=%%i
if not "%version:64-Bit=%" == "%version%" (
  set ARCH=64
) else (
  set ARCH=32
)

set PATH=%PATH%;%~dp0\..\lib\native\windows;%~dp0\..\lib\native\windows%ARCH%;%~dp0\..\lib\native\%ARCH%
set CYGWIN=nodosfilewarning
