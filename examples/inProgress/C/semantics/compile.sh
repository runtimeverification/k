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
username=`id -un`
baseMaterial=`mktemp -t $username-fsl-c-base.XXXXXXXXXXX`
programTemp=`mktemp -t $username-fsl-c-prog.XXXXXXXXXXX`
linkTemp=`mktemp -t $username-fsl-c-link.XXXXXXXXXXX`
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

#echo "0thatVariable=$@"
getoptsFunc "$@"
shift $(($OPTIND - 1))
#echo "after optshift=$@"
set +o nounset
#echo "now one=$1"
if [ -z "$1" ]; then # if after reading a round of arguments there isn't anything left that could be a filename...
	die "`printf \"$usage\" $(basename $0)`" 2
fi
set -o nounset
firstInputFile=$1
shift 1
#echo "after shift 1=$@"

getoptsFunc "$@"
shift $(($OPTIND - 1))
#echo "after second optshift=$@"
arguments="$@ $firstInputFile"
#echo "arguments=$arguments"
# if [ $(($# + 1)) -gt 1 ] && [ "$oval" ] && [ "$compileOnlyFlag" ]; then 
	# die "cannot specify -o with -c or -S with multiple files" 5
# fi

if [ -e `which readlink` ]; then
	READLINK=readlink
else
	if [ -e `which greadlink` ]; then
		READLINK=greadlink
	else
		die "No readlink/greadlink program found.  Cannot continue." 9
	fi 
fi
# echo "before: $linkTemp"
# this helps set the path correctly on windows
set +o errexit
newLinkTemp=`cygpath -u $linkTemp &> /dev/null` 
if [ "$?" -eq 0 ]; then
	linkTemp=`cygpath -u $linkTemp`
fi
set -o errexit
# echo "after: $linkTemp"
#echo "$arguments"
compiledPrograms=
for ARG in $arguments
do
	#echo "compiling $ARG"
	set +o errexit
	inputFile=`$READLINK -f $ARG`
	if [ "$?" -ne 0 ]; then
		die "`printf \"Input file %s does not exist\n\" $ARG`" 1
	fi
	inputDirectory=`dirname $inputFile`
	baseName=`basename $inputFile .c`
	maudeInput=$inputDirectory/$baseName.gen.maude
	localOval="$baseName.o"
	set -o errexit
	
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
	
	mv program-$baseName-compiled.maude $localOval
	compiledPrograms="$compiledPrograms $localOval"
	set -o errexit
	if [ "$compileOnlyFlag" ]; then
		if [ "$oflag" ]; then
			mv $localOval $oval
		fi
	fi
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
	maude="maude -no-wrap -no-banner \$0 $runner"
	debug="$mStart; $mDebug; echo erew in C-program-linked : \\($term\\) . >> $runner"
	run="$mStart; $exec; echo q >> $runner"
	prelude="--- &> /dev/null; if [ -t 0 ]; then stdin=\"\"; else stdin=\$(cat); fi; FSL_C_RUNNER=$freshFilename"
	echo "$prelude; if [ \$DEBUG ]; then $debug; $maude -ansi-color; else $run; $maude | perl $myDirectory/wrapper.pl \$PLAIN; fi; retval=\$?; rm -f $runner; exit \$retval" > $programTemp
	cat $baseMaterial | perl $myDirectory/slurp.pl >> $programTemp
	if [ ! "$dumpFlag" ]; then
		rm -f $linkTemp
	fi
	chmod u+x $programTemp
	mv $programTemp $oval
fi
cleanup




