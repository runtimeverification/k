#!/bin/bash
CIL_FLAGS="--noWrap --decil --noPrintLn --warnall --strictcheck --nokeepunused --envmachine"
PEDANTRY_OPTIONS="-Wall -Wextra -Werror -Wmissing-prototypes -pedantic -x c -std=c99"
GCC_OPTIONS="-nostdlib -nodefaultlibs -U __GNUC__"
myDirectory=`dirname $0`

if [ -e `which readlink` ]; then
	READLINK=readlink
else
	if [ -e `which greadlink` ]; then
		READLINK=greadlink
	else
		die "No readlink/greadlink program found.  Cannot continue." 9
	fi 
fi

K_MAUDE_BASE=`$READLINK -f $myDirectory/../../../..`
K_PROGRAM_COMPILE="$K_MAUDE_BASE/tools/kcompile-program.sh"
CIL_MACHINE='short=2,1 int=4,1 long=4,1 long_long=8,1 pointer=4,1 enum=4,1 float=4,1 double=8,1 long_double=16,1 void=1 bool=1,1 fun=1,1 alignof_string=1 max_alignment=1 size_t=unsigned_long wchar_t=int char_signed=true const_string_literals=true big_endian=false __thread_is_keyword=false __builtin_va_list=false underscore_name=true'
CIL_BASE=`readlink -f $myDirectory/../cil`
CIL_SUBDIR=`ls --color=none $CIL_BASE/obj | sed 's/\([^ ]*\)/\1/'`
CIL_PLATFORM=$CIL_BASE/obj/$CIL_SUBDIR
# $CIL_BASE/obj/x86_LINUX
ACTUAL_CIL=$CIL_PLATFORM/cilly.asm.exe
export CIL_MACHINE

set -o nounset
#trap cleanup SIGHUP SIGINT SIGTERM
username=`id -un`
compilationLog=`mktemp -t $username-fsl-c-log.XXXXXXXXXXX`
dflag=
gflag=
nowarn=0
usage="Usage: %s: [-d] inputFileName\n"
function die {
	cleanup
	echo "$1" >&2
	exit $2
}
function cleanup {
	rm -f $compilationLog
}
while getopts 'g:dw' OPTION
do
	case $OPTION in
	d)	dflag=1
		;;
	g)	gflag=1
		gval="$OPTARG"
		;;
	w)	nowarn=1
		;;
	?)	die "`printf \"$usage\" $(basename $0)`" 2
		;;
  esac
done
shift $(($OPTIND - 1))

if [ ! "$1" ]; then
	die "filename expected" 3
fi
filename=`basename "$1" .c`
escapedFilename=`echo -n $filename | tr "_" "u"`
directoryname=`dirname "$1"`/
if [ ! -e $directoryname$filename.c ]; then
	die "$filename.c not found" 4
fi

# perl $myDirectory/embed.pl -d=ML -o=$filename.prepre.gen $directoryname$filename.c
# if [ "$?" -ne 0 ]; then 
	# die "Error generating ML annotations." 5
# fi

# this instead of above
cp $directoryname$filename.c $filename.prepre.gen

#gcc $PEDANTRY_OPTIONS $GCC_OPTIONS -E -iquote "." -iquote "$directoryname" -I "$myDirectory/includes" $filename.prepre.gen $myDirectory/includes/clib.h > $filename.pre.gen 2> $filename.warnings.log
gcc $PEDANTRY_OPTIONS $GCC_OPTIONS -E -iquote "." -iquote "$directoryname" -I "$myDirectory/includes" $filename.prepre.gen > $filename.pre.gen 2> $filename.warnings.log
if [ "$?" -ne 0 ]; then 
	die "Error running preprocessor: `cat $filename.warnings.log`" 6
fi
if [ ! "$nowarn" ]; then
	cat $filename.warnings.log >&2
fi
#echo "done with gcc"
if [ ! "$dflag" ]; then
	rm -f $filename.prepre.gen
else
	$ACTUAL_CIL $CIL_FLAGS --out $filename.cil $filename.pre.gen
fi
$myDirectory/cparser $CIL_FLAGS --out $filename.gen.maude.tmp $filename.pre.gen 2> $filename.warnings.log
if [ "$?" -ne 0 ]; then 
	rm -f $filename.gen.maude.tmp
	msg="Error running cil: `cat $filename.warnings.log`"
	rm -f $filename.warnings.log
	die "$msg" 7
fi
if [ ! "$nowarn" ]; then
	cat $filename.warnings.log >&2
fi
#echo "done with cil"
if [ ! "$dflag" ]; then
	rm -f $filename.warnings.log
	rm -f $filename.pre.gen
fi
mv $filename.gen.maude.tmp $filename.gen.maude

modelCheck=
grep -q 'START MODEL-CHECKING' "$directoryname$filename.c"
retval=$?
if [ $retval -eq 0 ]; then 
	modelCheck=1
fi
echo "load $myDirectory/c-total" > program-$filename-gen.maude
echo "mod C-PROGRAM is" >> program-$filename-gen.maude
echo "including C-SYNTAX ." >> program-$filename-gen.maude
echo "including MATCH-C-SYNTAX ." >> program-$filename-gen.maude
echo "including COMMON-C-CONFIGURATION ." >> program-$filename-gen.maude
cat $filename.gen.maude >> program-$filename-gen.maude
if [ $modelCheck ]; then
	startModel=`grep -n "START MODEL-CHECKING" $directoryname$filename.c | sed 's/^\([0-9]*\):.*$/\1/'`
	#echo $startModel
	startModel=$(($startModel + 1))
	endModel=`grep -n "END MODEL-CHECKING" $directoryname$filename.c | sed 's/^\([0-9]*\):.*$/\1/'`
	#echo $endModel
	endModel=$(($endModel - 1))
	#echo "start = $startModel"
	#echo "end = $endModel"
	modelModule=`sed -n $startModel,${endModel}p $directoryname$filename.c`
	echo -e "$modelModule" >> program-$filename-gen.maude
fi
if [ ! "$dflag" ]; then
	rm -f $filename.gen.maude
fi
echo -e "endm\n" >> program-$filename-gen.maude


if [ "$gflag" ]; then
	$K_PROGRAM_COMPILE $gval C C-PROGRAM program-$escapedFilename > $compilationLog
else
	$K_PROGRAM_COMPILE program-$filename-gen.maude C C-PROGRAM program-$escapedFilename > $compilationLog
fi

if [ "$?" -ne 0 ]; then
	#msg=
	#cat $compilationLog > errorMsgOMG.txt
	msg="Error compiling program: `cat $compilationLog`"
	rm -f $compilationLog
	die "$msg" 8
fi
if [ "$escapedFilename" != "$filename" ]; then 
	mv program-$escapedFilename-compiled.maude program-$filename-compiled.maude
fi
if [ ! "$dflag" ]; then
	rm -f program-$filename-gen.maude
fi
sed '1 d' program-$filename-compiled.maude > program-$filename-compiled.maude.tmp
mv program-$filename-compiled.maude.tmp program-$filename-compiled.maude

rm -f program-$filename-compiled.maude.tmp
cleanup
