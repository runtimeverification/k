#!/bin/sh

DIR=$(dirname $0)

rm -rf $DIR/files
mkdir $DIR/files
mkdir $DIR/files/nordir
chmod ugo-rwx $DIR/files/nordir
mkdir $DIR/files/dir
mkdir $DIR/files/dir2
ln -s . $DIR/files/selflink
echo "123456" > $DIR/files/file
