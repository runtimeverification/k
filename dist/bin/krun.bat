@ECHO off
java -ea -jar -Xmx1024m "%~dp0..\lib\java\k3.jar" -krun %*
