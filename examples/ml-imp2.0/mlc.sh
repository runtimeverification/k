#!/bin/bash

K_ROOTDIR=~/k-framework
K_TOOLSDIR=${K_ROOTDIR}/tools
KC=${K_TOOLSDIR}/kcompile-program.sh

ML_ROOTDIR=${K_ROOTDIR}/examples/ml-imp2.0
LANG_NAME=imp
LANG_SUFFIX=.c
LANG_NAME_UPPER=`echo ${LANG_NAME} | tr [:lower:] [:upper:]`
LANG_PARSERDIR=${ML_ROOTDIR}/parser

if [ ! "$1" ]; then
  echo "mlc: no input file"
  exit 1
fi
if [ ! -e $1 ]; then
  echo "$1: No such file or directory"
  exit 1
fi

PROG=`basename $1 ${LANG_SUFFIX} | tr [:upper:] [:lower:]`
PROG_DIR=`dirname $1`
PROG_NAME=prog-${PROG}
PROG_MOD=`echo ${LANG_NAME_UPPER}-${PROG_NAME} | tr [:lower:] [:upper:]`
SRC_PROG=${PROG}.maude

USES=`cat $1 | expand -t 2 | grep "^ *using " | sed -e "s/^ *using /including /" -e "s/; *\r\?$/ ./"`
DECLS=`cat $1 | expand -t 2 | grep "^ *vars\? " | sed -e "s/^ *vars\? /ops /" -e "s/ : / : -> /" -e "s/; *\r\?$/ ./"`
STMTS=`cat $1 | expand -t 2 | grep -v '^ *using ' | grep -v '^ *vars\? '`

echo -e
"
load ${ML_ROOTDIR}/${LANG_NAME}-syntax.k\n\
load ${ML_ROOTDIR}/${LANG_NAME}-compiled.maude\n\
\n\
kmod ${PROG_MOD} is\n\
including ${LANG_NAME_UPPER}-SYNTAX .\n\
${USES}\n\
\n\
${DECLS}\n\
\n\
syntax TranslationUnit ::= ${PROG_NAME}\n\
macro ${PROG_NAME} = (\n\
${STMTS}\n\
)\n\
endkm\n\
"
>${SRC_PROG}

${KC} ${SRC_PROG} ${LANG_MOD} ${PROG_MOD} ${PROG_NAME}
if [ "$?" -ne 0 ]; then 
  exit $?
fi

rm ${SRC_PROG}
mv ${PROG_NAME}-compiled.maude ${PROG}.maude

