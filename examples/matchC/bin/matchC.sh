#!/bin/bash

K_ROOT_DIR=~/k-framework
ML_ROOT_DIR=${K_ROOT_DIR}/examples/matchC
LANG_NAME=matchC
LANG_SUFFIX=.c
LANG_MODULE=`echo ${LANG_NAME} | tr [:lower:] [:upper:]`

K_TOOLS_DIR=${K_ROOT_DIR}/tools
ANTLR_ROOT_DIR=${K_TOOLS_DIR}/antlr
LANG_PARSER_DIR=${ML_ROOT_DIR}/parser
LANG_SEMANTICS_DIR=${ML_ROOT_DIR}/semantics
ML_LIB_DIR=${ML_ROOT_DIR}/lib
SMT_MAUDE_DIR=${K_TOOLS_DIR}/smt_maude

KC=${K_TOOLS_DIR}/kcompile-program.sh
KFLAGS=

JVM=java
CLASSPATH=${ANTLR_ROOT_DIR}/antlrworks-1.4.jar:${ANTLR_ROOT_DIR}:${LANG_PARSER_DIR}
JFLAGS="-classpath ${CLASSPATH}"
UNWRAP_MAIN=unwrapBuiltinsMain
PARSER_MAIN=kernelCPreK

MAUDE=${SMT_MAUDE_DIR}/maude
MFLAGS=-no-banner

TMP_OUT=.tmp_out_file
TMP_ERR=.tmp_err_file

if [ ! "$1" ]; then
  echo "mlc: no input file"
  exit 1
fi
if [ ! -e $1 ]; then
  echo "$1: No such file or directory"
  exit 1
fi

PROG=`basename $1 ${LANG_SUFFIX}`
PROG_DIR=`dirname $1`
PROG_MODULE=PROG
PROG_MACRO=prog
MAUDE_PROG=${PROG}.maude
COMPILED_PROG=prog-compiled.maude
ML_PROG=${PROG}-ml.maude

PROG_BODY=`grep -v '^#include' $1 | grep -v 'printf(' | ${JVM} ${JFLAGS} ${PARSER_MAIN}`
if [ "$?" -ne 0 ]; then exit $?; fi

echo -e "
load ${ML_LIB_DIR}/ml-prelude.maude\n\
load ${LANG_SEMANTICS_DIR}/${LANG_NAME}-syntax.maude\n\
load ${LANG_SEMANTICS_DIR}/${LANG_NAME}-flat-compiled.maude\n\
mod ${PROG_MODULE} is\n\
including ${LANG_MODULE}-SYNTAX + MATHEMATICAL-DOMAIN-BUILTIN-MODULE + LIST-HP + BINARY-TREE-HP .\n\
${PROG_BODY}\n\
endm\n\
" >${MAUDE_PROG}

${KC} ${KFLAGS} ${MAUDE_PROG} ${LANG_MODULE} ${PROG_MODULE} ${PROG_MACRO} >${TMP_ERR}
if [ "$?" -ne 0 ]; then ERR=$?; cat ${TMP_ERR}; rm ${TMP_ERR}; exit ${ERR}; fi

UNWRAPED_BODY=`${JVM} ${JFLAGS} ${UNWRAP_MAIN} <${COMPILED_PROG} | grep -v '^load "list"'`
if [ "$?" -ne 0 ]; then exit $?; fi

echo -e "
load ${ML_LIB_DIR}/ml-prelude.maude\n\
load ${LANG_SEMANTICS_DIR}/${LANG_NAME}-uw.maude\n\
load ${ML_LIB_DIR}/fol.maude\n\
${UNWRAPED_BODY}\n\
mod TEST is inc ${LANG_MODULE}-${PROG_MACRO} + FOL= . endm\n\
set print attribute on .\n\
rew check('prog) .\n\
q\n\
" >${ML_PROG}

${MAUDE} ${MFLAGS} ${ML_PROG} >${TMP_OUT} 2>${TMP_ERR}
if [ "$?" -ne 0 ]; then ERR=$?; cat ${TMP_ERR}; rm ${TMP_ERR}; exit ${ERR}; fi

sed -e '1,2d' -e '$d' ${TMP_OUT}
#rm -f ${TMP_OUT} ${TMP_ERR} ${MAUDE_PROG} ${COMPILED_PROG} ${ML_PROG}

