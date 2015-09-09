@ECHO off
SETLOCAL ENABLEEXTENSIONS
IF ERRORLEVEL 1 ECHO Unable to enable extensions
call "%~dp0\setenv.bat"
SET K_OPTS=-Xms64m -Xmx1024m -Xss32m -XX:+TieredCompilation %K_OPTS%
ng.exe ng-version > NUL 2>&1
IF NOT ERRORLEVEL 1 (
  ng.exe org.kframework.main.Main %*
) ELSE (
  java  -Djava.awt.headless=true -ea %K_OPTS% -cp "%~dp0..\lib\java\*" org.kframework.main.Main %*
)
::don't call endlocal because that would reset ERRORLEVEL
