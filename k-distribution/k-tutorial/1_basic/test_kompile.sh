#!/usr/bin/env bash
set -ex
export PATH="$PATH:`cd "$(dirname "$0")"; pwd`/../../target/release/k/bin"
parallel -v < commands.sh
