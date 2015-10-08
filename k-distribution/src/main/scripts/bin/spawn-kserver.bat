@ECHO off
SETLOCAL ENABLEEXTENSIONS
IF ERRORLEVEL 1 ECHO Unable to enable extensions
start wscript "%~dp0\invisible.vbs" "%~dp0\kserver.bat" >  %1
exit
