@ECHO off
SETLOCAL ENABLEEXTENSIONS
IF ERRORLEVEL 1 ECHO Unable to enable extensions
call "%~dp0\..\lib\setenv.bat"
SET K_OPTS=-Xms64m -Xmx4096m -Xss32m -XX:+TieredCompilation %K_OPTS%
java -Dfile.encoding=UTF-8 -Djava.awt.headless=true -Djansi.force=true %K_OPTS% -ea -cp "%~dp0..\lib\java\*" org.kframework.main.Main -kserver %*
::don't call endlocal because that would reset ERRORLEVEL
