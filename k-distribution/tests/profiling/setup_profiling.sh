#!/bin/bash

set -euxo pipefail

export DEBIAN_FRONTEND=noninteractive
export BENCHER_VERSION="0.3.23"
apt-get update
apt-get upgrade --yes
apt-get install --yes python3 python3-pip git curl make time sudo wget
python3 -m pip install python-slugify

wget https://github.com/bencherdev/bencher/releases/download/v"${BENCHER_VERSION}"/bencher_"${BENCHER_VERSION}"_amd64.deb
sudo dpkg -i bencher_"${BENCHER_VERSION}"_amd64.deb
