#!/usr/bin/env bash
set -o errexit
set -o nounset
dumpFlag=
oflag=
usage="Usage: %s: [-o outputFileName] inputFileName\n"
oval=
warnFlag=
cil=~/k-framework/branches/2.0.1/examples/C/cil/obj/x86_LINUX/cilly.asm.exe
CIL_MACHINE='short=2,1 int=4,1 long=4,1 long_long=8,1 pointer=4,1 enum=4,1 float=4,1 double=8,1 long_double=16,1 void=1 bool=1,1 fun=1,1 alignof_string=1 max_alignment=1 size_t=unsigned_long wchar_t=int char_signed=true const_string_literals=true big_endian=false __thread_is_keyword=false __builtin_va_list=true underscore_name=true'
export CIL_MACHINE
inputFile=
function getoptsFunc {
	while getopts ':do:vw' OPTION
	do
		case $OPTION in
		d)	dumpFlag="-d"
			;;
		o)	oflag=1
			oval="$OPTARG"
			;;
		v)	printf "cilcc version 0.0.1"
			exit 0
			;;
		w)	warnFlag="-w"
			;;
		?)	if [ ! -f "$inputFile" ]; then
				printf "$usage" $(basename $0) >&2
				exit 2
			fi
			;;
	  esac
	done
}
getoptsFunc "$@"
shift $(($OPTIND - 1))
set +o nounset
if [ -z "$1" ]; then
	printf "$usage" $(basename $0) >&2
	exit 2
fi
set -o nounset
set +o errexit
inputFile=`readlink -f $1`
if [ "$?" -ne 0 ]; then
	printf "Input file %s does not exist\n" $1
	exit 1
fi
set -o errexit

shift 1
inputDirectory=`dirname $inputFile`
baseName=`basename $inputFile .c`

if [ ! "$oflag" ]; then
	oval="a.out"
fi
rm -f $oval

preproc=`mktemp -t \`whoami\`-fsl-c.XXXXXXXXXXX`
cilout=`mktemp -t \`whoami\`-fsl-c.XXXXXXXXXXX`

getoptsFunc "$@"
shift $(($OPTIND - 1))

set +o errexit
gcc -U __GNUC__ -pedantic -std=c99 -E -o $preproc $inputFile &> preproc.err.log
if [ "$?" -ne 0 ]; then
	echo "Error preprocessing"
	cat preproc.err.log
	exit 2
fi
$cil --noWrap --decil --noPrintLn --warnall --strictcheck --nokeepunused --envmachine --out $cilout $preproc &> cil.err.log
if [ "$?" -ne 0 ]; then
	echo "Error running cil"
	cat cil.err.log
	exit 3
fi
gcc -m32 -O0 -U __GNUC__ -pedantic -std=c99 -x c -o $oval $cilout &> gcc.err.log
retval="$?"
if [ $retval -ne 0 ]; then
	echo "Error running gcc"
	cat gcc.err.log
	exit 4
fi
set -o errexit
rm -f $preproc
rm -f $cilout
exit $retval