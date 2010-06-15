k_rootdir=~/k-framework
k_toolsdir=${k_rootdir}/tools
antlr_rootdir=${k_toolsdir}/antlr
makefile=Makefile.antlr
target=run
main=unwrapBuiltinsMain
filepath=${1%/*}
kmaude_file=${1##*/}
filename=${kmaude_file%%.*}
maude_file=${filename}".maude"
syntax_file=${filename}"-syntax.maude"
semantics_file=${filename}"-semantics.maude"
compiled_file=${filename}"-compiled.maude"
ml_file="ml-"${filename}".maude"
cwd=`pwd`

${k_toolsdir}/kompile.pl $1
python format.py ${compiled_file} | (cd ${antlr_rootdir} && make -f ${makefile} ${target} MAIN=${main}) | sed "1d" | sed "s/subsort Int\+\+ < Builtins \./\0\nsubsort Int\+\+ < KResult \.\nsubsort Id < K \./g" >${cwd}/${ml_file}

