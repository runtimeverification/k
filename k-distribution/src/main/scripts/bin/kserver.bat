@ECHO off
SETLOCAL ENABLEEXTENSIONS
IF ERRORLEVEL 1 ECHO Unable to enable extensions
call "%~dp0\setenv.bat"
IF NOT DEFINED K_OPTS SET K_OPTS=-Xms64m -Xmx24G -Xss32m -XX:ReservedCodeCacheSize=512m
java -Djava.awt.headless=true -Djansi.force=true %K_OPTS% -ea -cp "%~dp0..\lib\java\*" com.martiansoftware.nailgun.NGServer %*
ENDLOCAL
