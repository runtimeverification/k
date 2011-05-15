#!/usr/bin/env bash

cat $1 | python parser.py | maude -no-wrap | perl wrapper.pl
