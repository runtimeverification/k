for /f "delims=" %%i in ('ng org.kframework.main.JavaVersion 2^>^&1') do set VERSION=%%i
set INCOMPLETE=0
if not "%version:64-Bit=%" == "%version%" (
  set ARCH=64
  set JAVA=ng
) else if not "%version:connect: No error=%" == "%version%" (
  for /f "delims=" %%i in ('java -version 2^>^&1') do set VERSION=%%i
  set INCOMPLETE=1
) else (
  set ARCH=32
  set JAVA=ng
)
if %INCOMPLETE% == 1 (
  if not "%version:64-Bit=%" == "%version%" (
    set ARCH=64
    set TIERED=-XX:+TieredCompilation
  ) else (
    set ARCH=32
  )
  set K_OPTS=-Xms64m -Xmx4096m -Xss32m %TIERED% %K_OPTS%
  set INCOMPLETE=2
)
if %INCOMPLETE%==2 (
  set JAVA=java -Djava.awt.headless=true %K_OPTS% -ea -cp "%~dp0..\lib\java\*" 
)
