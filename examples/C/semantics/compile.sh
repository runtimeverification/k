#!/bin/bash 
set -o errexit
set -o nounset
#trap cleanup SIGHUP SIGINT SIGTERM
dumpFlag=
oflag=
usage="Usage: %s: [-o outputFileName] inputFileName\n"
oval=
gflag=
warnFlag=
myDirectory=`dirname $0`
inputFile=
compileOnlyFlag=
username=`whoami`
baseMaterial=`mktemp -t $username-fsl-c.XXXXXXXXXXX`
programTemp=`mktemp -t $username-fsl-c.XXXXXXXXXXX`
linkTemp=`mktemp -t $username-fsl-c.XXXXXXXXXXX`
stdlib="$myDirectory/lib/clib.o"
baseName=
libFlag=
function die {
	cleanup
	echo "$1" >&2
	exit $2
}
function cleanup {
	rm -f $baseMaterial
	rm -f $programTemp
	rm -f $linkTemp
}
function getoptsFunc {
	while getopts ':cdg:o:vsw' OPTION
	do
		case $OPTION in
		c)	compileOnlyFlag="-c"
			;;
		d)	dumpFlag="-d"
			;;
		g)	gflag=1
			gval="$OPTARG"
			;;
		o)	oflag=1
			oval="$OPTARG"
			;;
		v)	printf "kcc version 0.0.1"
			exit 0
			;;
		w)	warnFlag="-w"
			;;
		s)	libFlag="-s"
			;;
		?)	if [ ! "$inputFile" ] && [ ! "$firstInputFile" ] ; then
				die "`printf \"$usage\" $(basename $0)`" 2
			fi
			;;
	  esac
	done
}

getoptsFunc "$@"
shift $(($OPTIND - 1))
set +o nounset
if [ -z "$1" ]; then # if after reading a round of arguments there isn't anything left that could be a filename...
	die "`printf \"$usage\" $(basename $0)`" 2
fi
set -o nounset
firstInputFile=$1
shift 1
getoptsFunc "$@"
#echo $(($# + 1)) 
shift $(($OPTIND - 1))
arguments="$@ $firstInputFile"

# if [ $(($# + 1)) -gt 1 ] && [ "$oval" ] && [ "$compileOnlyFlag" ]; then 
	# die "cannot specify -o with -c or -S with multiple files" 5
# fi

#echo "$arguments"
compiledPrograms=
for ARG in $arguments
do
	#echo "compiling $ARG"
	set +o errexit
	inputFile=`readlink -f $ARG`
	if [ "$?" -ne 0 ]; then
		die "`printf \"Input file %s does not exist\n\" $ARG`" 1
	fi
	set -o errexit

	inputDirectory=`dirname $inputFile`
	baseName=`basename $inputFile .c`

	maudeInput=$inputDirectory/$baseName.gen.maude
	
	if [ ! "$oflag" ]; then
		oval="$baseName.o"
	fi
	
	if [ "$gflag" ]; then
		garg="-g $gval"
	else 
		garg=""
	fi

	set +o errexit
	$myDirectory/compileProgram.sh $garg $warnFlag $dumpFlag $inputFile
	if [ "$?" -ne 0 ]; then
		die "compilation failed" 3
	fi
	
	mv program-$baseName-compiled.maude $oval
	compiledPrograms="$compiledPrograms $oval" 
	set -o errexit
done

#echo $compiledPrograms
if [ ! "$compileOnlyFlag" ]; then
	if [ ! "$oflag" ]; then
		oval="a.out"
	fi
	mv $linkTemp "$linkTemp.maude"
	linkTemp="$linkTemp.maude"
	echo "mod C-program-linked is including C ." > $linkTemp
	if [ "$libFlag" ]; then
		perl $myDirectory/link.pl $compiledPrograms >> $linkTemp
	else
		perl $myDirectory/link.pl $compiledPrograms $stdlib >> $linkTemp
	fi
	echo "endm" >> $linkTemp
	#echo $linkTemp
	#mv program-$baseName-linked.tmp program-$baseName-linked.maude
	if [ ! "$dumpFlag" ]; then
		rm -f $compiledPrograms
	fi
	echo "load $myDirectory/c-total" > $baseMaterial
	echo "load $linkTemp" >> $baseMaterial
	runner='$FSL_C_RUNNER'
	mStart="echo > $runner"
	freshFilename='`mktemp -t fsl-c.XXXXXXXXXXX`'
	term="eval\\(linked-program, \\(\`for i in \$0 \"\$@\"; do echo \"String \\\"\$i\\\"(.List{K}),,\" ; done\` .List{K}\\), \\\"\$stdin\\\"\\)"
	exec="echo erew in C-program-linked : $term . >> $runner"
	mDebug="echo break select debug . >> $runner; echo set break on . >> $runner"
	maude="maude -no-wrap \$0 $runner"
	debug="$mStart; $mDebug; echo erew in C-program-linked : \\($term\\) . >> $runner"
	run="$mStart; $exec; echo q >> $runner"
	prelude="--- &> /dev/null; if [ -t 0 ]; then stdin=\"\"; else stdin=\$(cat); fi; FSL_C_RUNNER=$freshFilename"
	echo "$prelude; if [ \$DEBUG ]; then $debug; $maude -ansi-color; else $run; $maude | perl $myDirectory/wrapper.pl; fi; retval=\$?; rm -f $runner; exit \$retval" > $programTemp
	cat $baseMaterial | perl $myDirectory/slurp.pl >> $programTemp
	if [ ! "$dumpFlag" ]; then
		rm -f $linkTemp
	fi
	chmod u+x $programTemp
	mv $programTemp $oval
fi
cleanup




