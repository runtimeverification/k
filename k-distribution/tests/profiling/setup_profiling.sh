#!/bin/bash

set -euxo pipefail

export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get upgrade --yes
apt-get install --yes make time
apt-get install --yes ./kframework.deb
