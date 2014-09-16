@ECHO off
set PATH=%PATH%;"%~dp0..\lib\native"
SETLOCAL ENABLEEXTENSIONS
IF ERRORLEVEL 1 ECHO Unable to enable extensions
IF NOT DEFINED K_OPTS SET K_OPTS=-Xms64m -Xmx1024m -Xss32m -XX:+TieredCompilation
java  -Djava.awt.headless=true %K_OPTS% -ea -jar "%~dp0..\lib\java\k-${artifact.version}.jar" -ktest %*
ENDLOCAL
