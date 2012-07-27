@ECHO off
java -ss8m -Xms64m -Xmx1G -jar "%~dp0java\k3.jar" -kompile %*
