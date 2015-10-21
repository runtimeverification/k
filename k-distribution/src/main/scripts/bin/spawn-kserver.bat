@ECHO off
SETLOCAL ENABLEEXTENSIONS
IF ERRORLEVEL 1 ECHO Unable to enable extensions
set PATH=%PATH%;C:\RV-Match\msys\usr\bin;C:\RV-Match\msys\mingw32\bin
start wscript "%~dp0..\lib\invisible.vbs" "%~dp0\kserver.bat" 
exit
