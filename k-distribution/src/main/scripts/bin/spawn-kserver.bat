@ECHO off
SETLOCAL ENABLEEXTENSIONS
IF ERRORLEVEL 1 ECHO Unable to enable extensions
set PATH=C:\RV-Match\msys2\usr\bin;C:\RV-Match\msys2\mingw32\bin;%PATH%
start wscript "%~dp0..\lib\invisible.vbs" "%~dp0\kserver.bat" 
exit
