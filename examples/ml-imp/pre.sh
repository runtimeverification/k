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

${k_toolsdir}/kmaude2maude.pl $1
cat ${maude_file} | sed "s/ + +/++/g" | sed "s/== =/===/g" | sed "s/\* \*\*/\*\*\*/g" > ${maude_file}
cat ${syntax_file} | sed "s/ + +/++/g" | sed "s/== =/===/g" | sed "s/\* \*\*/\*\*\*/g" > ${syntax_file}
cat ${semantics_file} | sed "s/ + +/++/g" | sed "s/== =/===/g" | sed "s/\* \*\*/\*\*\*/g" > ${semantics_file}
${k_toolsdir}/kcompile.sh ${maude_file}
(cd ${antlr_rootdir} && make -f ${makefile} ${target} MAIN=${main}) < ${compiled_file} | sed "1d" | sed "s/subsort Int++ < Builtins ./\0\nsubsort Int++ < K ./g" > ${cwd}/${ml_file}
