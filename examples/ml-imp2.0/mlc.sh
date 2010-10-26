#!/bin/bash

K_ROOT_DIR=~/k-framework
ML_ROOT_DIR=${K_ROOT_DIR}/examples/ml-imp2.0
LANG_NAME=imp
LANG_SUFFIX=.c
LANG_MODULE=`echo ${LANG_NAME} | tr [:lower:] [:upper:]`

K_TOOLS_DIR=${K_ROOT_DIR}/tools
ANTLR_ROOT_DIR=${K_TOOLS_DIR}/antlr
LANG_PARSER_DIR=${ML_ROOT_DIR}/parser

KC=${K_TOOLS_DIR}/kompile.pl
KFLAGS="-c -l ${LANG_MODULE}"

JVM=java
CLASSPATH=${ANTLR_ROOT_DIR}/antlrworks-1.4.jar:${ANTLR_ROOT_DIR}:${LANG_PARSER_DIR}
JFLAGS="-classpath ${CLASSPATH}"
UNWRAP_MAIN=unwrapBuiltinsMain
PARSER_MAIN=kernelCPreK

MAUDE=maude

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
MAUDE_PROG=${PROG}.maude
COMPILED_PROG=${PROG}-compiled.maude
ML_PROG=${PROG}-ml.maude

${JVM} ${JFLAGS} ${PARSER_MAIN} <$1 >${MAUDE_PROG}
if [ "$?" -ne 0 ]; then exit $?; fi

sed -i -e "1i load ${ML_ROOT_DIR}/${LANG_NAME}-semantics.maude" ${MAUDE_PROG}
echo -e "mod ${LANG_MODULE} is inc ${LANG_MODULE}-SEMANTICS + PROG . endm" >>${MAUDE_PROG}

${KC} ${KFLAGS} ${MAUDE_PROG}
if [ "$?" -ne 0 ]; then exit $?; fi

${JVM} ${JFLAGS} ${UNWRAP_MAIN} <${COMPILED_PROG} >${ML_PROG}
if [ "$?" -ne 0 ]; then exit $?; fi

sed -i -e "/^mod ${LANG_MODULE} is/a \
subsort Formula Subst MathObj++ List{MathObj++} Set{MathObj++} Value TypedValue ExpressionType < Builtins KResult . \
subsort Id Field < Builtins KProper ." ${ML_PROG}
echo -e "load ${ML_ROOT_DIR}/fol.maude\n\
mod TEST is inc FOL= . endm\n\
rew check('prog) .
q" >>${ML_PROG}

${MAUDE} ${ML_PROG}
if [ "$?" -ne 0 ]; then exit $?; fi

rm ${MAUDE_PROG} ${COMPILED_PROG} #${ML_PROG}

#${KC} ${SRC_PROG} ${LANG_MOD} ${PROG_MOD} ${PROG_NAME}
#if [ "$?" -ne 0 ]; then 
#  exit $?
#fi
