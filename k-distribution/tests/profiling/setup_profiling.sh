#!/bin/bash

set -euxo pipefail

export DEBIAN_FRONTEND=noninteractive
export BENCHER_VERSION="0.3.10"
apt-get update
apt-get upgrade --yes
apt-get install --yes make time sudo wget
apt-get install --yes ./kframework.deb

wget https://github.com/bencherdev/bencher/releases/download/v"${BENCHER_VERSION}"/bencher_"${BENCHER_VERSION}"_amd64.deb
sudo dpkg -i bencher_"${BENCHER_VERSION}"_amd64.deb
