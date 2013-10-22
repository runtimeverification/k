@ECHO off
SETLOCAL ENABLEEXTENSIONS
IF ERRORLEVEL 1 ECHO Unable to enable extensions
IF NOT DEFINED K_OPTS SET K_OPTS=-Xms64m -Xmx1024m -Xss32m
java -ea -jar %K_OPTS% "%~dp0..\lib\java\k3.jar" -kcheck %*
ENDLOCAL
