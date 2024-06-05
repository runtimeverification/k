#!/usr/bin/env bash

set -euxo pipefail

SPHINX_VERSION=7.2.6

DOCS_DIR=$(dirname $0)
PYK_DIR=$DOCS_DIR/..

VENV_DIR=$(mktemp -d --suffix -pyk-docs-venv)
trap 'rm -rf $VENV_DIR' EXIT

python3 -m venv $VENV_DIR
source $VENV_DIR/bin/activate

pip install --upgrade pip
pip install --editable $PYK_DIR
pip install sphinx==$SPHINX_VERSION

# Generate and install _kllvm
PYTHON_LIB=$(find $VENV_DIR -name 'site-packages' -type d)
python3 -c "from pyk.kllvm.compiler import compile_kllvm; compile_kllvm('$PYTHON_LIB', verbose=True)"

sphinx-apidoc $PYK_DIR/src/pyk --output $DOCS_DIR/api --force --separate --module-first
sphinx-build -b html docs $DOCS_DIR/build
