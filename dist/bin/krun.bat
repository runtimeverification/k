@ECHO off
set PATH=%PATH%;%~dp0..\lib\native\cygwin;%~dp0..\lib\native\cygwin\x64
java -ea -jar -Xmx1024m "%~dp0..\lib\java\k3.jar" -krun %*
