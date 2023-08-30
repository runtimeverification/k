#!/bin/bash

set -euxo pipefail

export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get upgrade --yes
apt-get install --yes make time sudo wget
apt-get install --yes ./kframework.deb

wget https://github.com/bencherdev/bencher/releases/download/v0.3.9/bencher_0.3.9_amd64.deb
sudo dpkg -i bencher_0.3.9_amd64.deb
