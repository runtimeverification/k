#!/bin/bash
#set -x

K_ROOT_DIR=~/k-framework
ML_ROOT_DIR=${K_ROOT_DIR}/examples/matchC
LANG_NAME=matchC
LANG_SUFFIX=.c
LANG_MODULE=`echo ${LANG_NAME} | tr [:lower:] [:upper:]`

K_TOOLS_DIR=${K_ROOT_DIR}/tools
ANTLR_ROOT_DIR=${K_TOOLS_DIR}/antlr
LANG_PARSER_DIR=${ML_ROOT_DIR}/parser
LANG_SEMANTICS_DIR=${ML_ROOT_DIR}/semantics
ML_BIN_DIR=${ML_ROOT_DIR}/bin
ML_LIB_DIR=${ML_ROOT_DIR}/lib


KC=${K_TOOLS_DIR}/kcompile-program.sh
KFLAGS=

JVM=java
CLASSPATH=${ANTLR_ROOT_DIR}/antlrworks-1.4.jar:${ANTLR_ROOT_DIR}:${LANG_PARSER_DIR}
JFLAGS="-classpath ${CLASSPATH}"
PARSER_MAIN=KernelCPreK

PYTHON=python

SMT_MAUDE_DIR=${K_TOOLS_DIR}/smt_maude
#MAUDE=${SMT_MAUDE_DIR}/maude
MAUDE=maude
MFLAGS="-no-banner -no-wrap"
MAUDE_RUNNER=${ML_BIN_DIR}/maude_runner.py

OUT_FILTER_DIR=${K_TOOLS_DIR}/OutputFilter
OUT_FILTER=${OUT_FILTER_DIR}/filterOutput
OUT_FILTER_STYLE=${ML_BIN_DIR}/primitive_style.yml

TMP_OUT=.tmp_out_file
TMP_ERR=.tmp_err_file

while getopts 'eco:' OPTION; do
  case $OPTION in
    c) COMPILE_FLAG="-c"
       ;;
    e) EXEC_FLAG="-e"
       ;;
    o) OUT_FLAG='-o'
       ML_PROG="$OPTARG"
       ;;
    ?) ;; 
  esac
done
shift $(($OPTIND - 1))
if [ -z "$1" ]; then
  echo "matchC: no input file"
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
MAUDE_PROG=${PROG_MACRO}.maude
COMPILED_PROG=${PROG_MACRO}-compiled.maude
if [ -z "${OUT_FLAG}" ]; then
  ML_PROG=${PROG}.maude
fi
if [ -z "${EXEC_FLAG}" ]; then
  ML_OP=check
else
  ML_OP=run
fi

echo -e "
load ${LANG_SEMANTICS_DIR}/${LANG_NAME}-compiled.maude\n\
load ${ML_LIB_DIR}/utils.maude\n\
mod ${PROG_MODULE} is
inc ${LANG_MODULE} .
" >${ML_PROG}

TIME_CMD="/usr/bin/time -f %e -o ${TMP_OUT}"
PROG_CMD="grep -v ^#include $1 | ${JVM} ${JFLAGS} ${PARSER_MAIN} >>${ML_PROG}"
echo -e -n "Compiling program ... "
${TIME_CMD} bash -c "${PROG_CMD}"
if [ "$?" -ne 0 ]; then exit $?; fi
echo -e "DONE! [\033[1;33m`cat ${TMP_OUT}`s\033[0m]"

echo -e "
endm\n\
mod TEST is inc ${PROG_MODULE} + UTILS . endm\n\
set print attribute on .\n
rew ${ML_OP}(prog) .\n
q\n\
" >>${ML_PROG}

if [ -z "${COMPILE_FLAG}" ]; then
  #${MAUDE} ${MFLAGS} ${ML_PROG} >${TMP_OUT} 2>${TMP_ERR}
  ${PYTHON} ${MAUDE_RUNNER} ${ML_PROG} 2>${TMP_ERR}
  if [ "$?" -ne 0 ]; then ERR=$?; cat ${TMP_ERR}; rm ${TMP_ERR}; exit ${ERR}; fi
  cat ${TMP_ERR}

  grep 'rewrites: ' ${TMP_OUT}
  ${OUT_FILTER} ${TMP_OUT} ${OUT_FILTER_STYLE}
  if [ "$?" -ne 0 ]; then exit $?; fi
fi

#rm -f ${TMP_OUT} ${TMP_ERR} ${MAUDE_PROG} ${COMPILED_PROG}
if [ -z "${COMPILE_FLAG}" -a -z "${OUT_FLAG}" ]; then
  rm -f ${ML_PROG}
fi

