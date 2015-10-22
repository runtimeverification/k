@ECHO off
set PATH=%~dp0..\lib\native\windows;%PATH%
call "%~dp0..\lib\checkJava.bat" :: sets ARCH and JAVA

set PATH=%~dp0..\lib\native\windows%ARCH%;%~dp0..\lib\native\%ARCH%;%PATH%
set CYGWIN=nodosfilewarning
