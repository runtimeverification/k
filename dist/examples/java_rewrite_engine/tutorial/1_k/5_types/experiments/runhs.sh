#!/bin/bash
time (ghc -dshow-passes -c $1 2>&1 | grep -q Desugar || echo failed)
