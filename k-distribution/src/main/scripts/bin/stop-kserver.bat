@ECHO off
SETLOCAL ENABLEEXTENSIONS
IF ERRORLEVEL 1 ECHO Unable to enable extensions
call "%~dp0..\lib\setenv.bat"
ng.exe org.kframework.kserver.KServerFrontEnd
