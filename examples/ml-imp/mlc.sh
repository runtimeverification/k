#!/bin/bash

K_ROOTDIR=~/k-framework
ML_ROOTDIR=${K_ROOTDIR}/examples/ml-imp
K_TOOLSDIR=${K_ROOTDIR}/tools
KC=${K_TOOLSDIR}/kcompile-program.sh
LANG_NAME=imp
LANG_NAME_UPPER=`echo ${LANG_NAME} | tr [:lower:] [:upper:]`

if [ ! "$1" ]; then
  echo "mlc: no input file"
  exit 1
fi
PROG=`basename $1 .${LANG_NAME}`
PROG_DIR=`dirname $1`
if [ ! -e $1 ]; then
  echo "$1: No such file or directory"
  exit 1
fi
PROG_OP=prog-${PROG}
PROG_MOD=`echo ${LANG_NAME_UPPER}-${PROG_OP} | tr [:lower:] [:upper:]`
TMP_PROG=tmp-${PROG}.maude

USES=`cat $1 | expand -t 2 | grep "^ *using " | sed -e "s/^ *using /including/" -e "s/; *\r\?$/ ./"`
DECLS=`cat $1 | expand -t 2 | grep "^ *vars\? " | sed -e "s/^ *vars\? /ops /" -e "s/ : / : -> /" -e "s/; *\r\?$/ ./"`
STMTS=`cat $1 | expand -t 2 | grep -v '^ *using ' | grep -v '^ *vars\? '`
MOD="
load ${ML_ROOTDIR}/${LANG_NAME}-syntax.maude\n\
load ${ML_ROOTDIR}/${LANG_NAME}-compiled.maude\n\
\n\
mod ${PROG_MOD} is\n\
including ${LANG_NAME_UPPER}-SYNTAX .\n\
${USES}\n\
\n\
${DECLS}\n\
\n\
op ${PROG_OP} : -> Stmts .\n\
eq ${PROG_OP} = (\n\
${STMTS}\n\
) .\n\
endm\n\
"

echo -e ${MOD} >${TMP_PROG}
${KC} ${TMP_PROG} ${LANG_NAME_UPPER} ${PROG_MOD} ${PROG_OP}
if [ "$?" -ne 0 ]; then 
  exit $?
fi
rm ${TMP_PROG}
mv ${PROG_OP}-compiled.maude ${PROG}.maude

