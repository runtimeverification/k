@ECHO off
:: This is not designed for the users of K
:: It's justa simple script that I use to test the parsers.

cp -r ".k" "%~dp0\\..\\..\\javasources\\K3Syntax\\test"

cp ".\\.k\\def\\Integration.sdf" "%~dp0\\..\\..\\javasources\\K3Disamb\\syntax\\Integration.sdf"

