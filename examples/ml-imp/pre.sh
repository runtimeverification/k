k_rootdir=~/k-framework
k_toolsdir=${k_rootdir}/tools
antlr_rootdir=${k_toolsdir}/antlr
makefile=Makefile.antlr
target=run
main=unwrapBuiltinsMain
filepath=${1%/*}
kmaude_main_file=${1##*/}
filename=${kmaude_main_file%%.*}
syntax_file=${filename}"-syntax.maude"
semantics_file=${filename}"-semantics.maude"
main_file=${filename}".maude"
compiled_file=${filename}"-compiled.maude"
ml_file="ml-"${filename}".maude"
cwd=`pwd`

#${k_toolsdir}/kompile.pl -m $1
${k_toolsdir}/kompile.pl -m ${filename}
sed -i "s/\: : Int/: : IntSort/g" ${syntax_file}
sed -i "s/\: : Int/: : IntSort/g" ${semantics_file}
${k_toolsdir}/kompile.pl -c ${filename}
(cd ${antlr_rootdir} && make -f ${makefile} ${target} MAIN=${main}) <${compiled_file} | sed "1,3d" | sed "/sorts/a\subsort Id < KProper ." >${cwd}/${ml_file}

