#!/usr/bin/env bash
TMP_DIR=$(mktemp -d)
nix build .#k-lock --out-link $TMP_DIR/result
rm -rf mvn-lock
cp -r $TMP_DIR/result/lock mvn-lock
chmod -R u=rwx,g=rx,o=rx mvn-lock
find mvn-lock -type f -exec chmod u=rw,g=r,o=r {} \;
rm -r $TMP_DIR