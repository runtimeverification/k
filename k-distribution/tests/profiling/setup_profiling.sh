#!/bin/bash

set -euxo pipefail

export DEBIAN_FRONTEND=noninteractive
export BENCHER_VERSION="0.3.15"
apt-get update
apt-get upgrade --yes
apt-get install --yes python3 git curl make time sudo wget
# Build K if no flag was given and don't execute if flag was given
if [ $# -eq 0 ]; then
    apt-get install --yes ./kframework.deb
fi
python -m pip install python-slugify

wget https://github.com/bencherdev/bencher/releases/download/v"${BENCHER_VERSION}"/bencher_"${BENCHER_VERSION}"_amd64.deb
sudo dpkg -i bencher_"${BENCHER_VERSION}"_amd64.deb
