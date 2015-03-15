@ECHO off
SETLOCAL ENABLEEXTENSIONS
IF ERRORLEVEL 1 ECHO Unable to enable extensions
call "%~dp0\..\lib\setenv.bat"
IF NOT DEFINED K_OPTS SET K_OPTS=-Xms64m -Xmx4G -Xss32m -XX:+TieredCompilation
java -Djava.awt.headless=true -Djansi.force=true %K_OPTS% -ea -cp "%~dp0..\lib\java\*" org.kframework.main.Main -kserver %*
ENDLOCAL
