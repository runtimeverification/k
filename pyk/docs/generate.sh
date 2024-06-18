#!/usr/bin/env bash

set -euxo pipefail

SPHINX_VERSION=7.2.6

DOCS_DIR=$(realpath $(dirname $0))
API_DIR=$DOCS_DIR/api
BUILD_DIR=$DOCS_DIR/build

PYK_DIR=$(realpath $DOCS_DIR/..)
SRC_DIR=$PYK_DIR/src/pyk

rm -rf $API_DIR $BUILD_DIR

VENV_DIR=$(mktemp -d --suffix -pyk-docs-venv)
trap 'rm -rf $VENV_DIR' EXIT

python3 -m venv $VENV_DIR
source $VENV_DIR/bin/activate

pip install --upgrade pip
pip install --editable $PYK_DIR
pip install sphinx==$SPHINX_VERSION sphinx_rtd_theme

# Generate and install _kllvm
PYTHON_LIB=$(find $VENV_DIR -name 'site-packages' -type d)
python3 -c "from pyk.kllvm.compiler import compile_kllvm; compile_kllvm('$PYTHON_LIB', verbose=True)"

sphinx-apidoc $SRC_DIR --output $API_DIR --force --separate --module-first
sphinx-build -b html docs $BUILD_DIR

find $BUILD_DIR -depth -name '.*' -exec rm -rf {} \;
