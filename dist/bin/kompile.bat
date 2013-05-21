@ECHO off
java -ea -ss8m -Xms64m -Xmx1G -jar "%~dp0..\lib\java\k3.jar" -kompile %*
