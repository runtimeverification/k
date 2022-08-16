#!/usr/bin/env bash

set -euo pipefail

summary_script="$1" ; shift
source ../kit-shell
cd $(dirname ${summary_script})
source $(basename ${summary_script})
