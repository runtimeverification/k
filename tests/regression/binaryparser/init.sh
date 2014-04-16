#!/bin/sh
# Copyright (C) 2014 K Team. All Rights Reserved.
$kompile test.k
$krun -cPGM "a" --output binary --output-file 1.test
