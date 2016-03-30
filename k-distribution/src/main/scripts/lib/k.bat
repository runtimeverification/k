@ECHO off
SETLOCAL ENABLEEXTENSIONS
IF ERRORLEVEL 1 ECHO Unable to enable extensions
call "%~dp0\setenv.bat"
%JAVA% org.kframework.main.Main %*
::don't call endlocal because that would reset ERRORLEVEL
