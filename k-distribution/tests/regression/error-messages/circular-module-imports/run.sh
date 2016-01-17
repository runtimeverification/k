#!/bin/bash

for i in *.k.out; do
  kompile "${i%.out}" 2>&1 | grep -v 'Source' | diff - "$i"
done >>dummy.k
