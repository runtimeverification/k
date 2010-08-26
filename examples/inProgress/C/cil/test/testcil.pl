# A regression tester for CIL
#
# Note: comments now start with Bug/Notbug/Minor/Limitation to give some categorisation.

require 5.000;


# Packages to import.
use Getopt::Long;           # Command-line option processing
use File::Basename;         # File name parsing
use Cwd;                    # Directory navigation
use strict;
# use Data::Dumper;
use FindBin;
use lib "$FindBin::Bin/../ocamlutil";

use RegTest;

$ENV{LANG} = 'C';

print "Test infrastructure for CIL\n";

# Create our customized test harness
my $TEST = CilRegTest->new(AvailParams => { 'RUN' => 1,
                                            'SUCCESS' => 0},
                           LogFile => "cil.log",
                           CommandName => "testcil");

# sm: I want a global name for this $TEST thing, since I find it is merely
# excess verbiage when adding tests..
$main::globalTEST = $TEST;

my $inferbox="none";

# am I on win32?
my $win32 = ($^O eq 'MSWin32' || $^O eq 'cygwin');
my $unix = !$win32;
my $solaris = $^O eq 'solaris';


# operating modes
my $gcc =       "_GNUCC=1";     # sm: not sure where/why this is needed


# am I using egcs?
my $egcs = $unix && system("gcc -v 2>&1 | grep egcs >/dev/null")==0;

# am I on manju?
my $manju = $unix && system("hostname | grep manju >/dev/null")==0;

my $make;
if ($solaris) {
    $make = "gmake";
} else {
    $make = "make";
}

# We watch the log and we remember in what stage we are (so that we can
# interpret the error)

# Stages:
#  1000 - Start (scripts, preprocessors, etc.)
#  1001 - Parsing
#  1002 - cabs2cil
#  1003 - Compilation
#  1004 - Running 


my %commonerrors = 
    ("^Parsing " => sub { $_[1]->{instage} = 1001; },

     "^Converting CABS" => sub { $_[1]->{instage} = 1002; },

     "^Linked the cured program" => sub { $_[1]->{instage} = 1008; },

# We are seeing an error from make. Try to classify it based on the stage
# in which we are
     "^make: \\*\\*\\*" => 
     sub { 
         if($_[1]->{ErrorCode} == 0) {
             $_[1]->{ErrorCode} = $_[1]->{instage};
         }},
    
    #"[sS]yntax error" => sub { $_[1]->{ErrorCode} = 1000; },
    
         # Collect some more parameters
         # Now error messages
    "^((Error|Bug|Unimplemented): .+)\$" 
                      => sub { if(! defined $_[1]->{ErrorMsg}) {
                                 $_[1]->{ErrorMsg} = $_[2];} },
    "^(.+ : error .+)\$" => sub { if(! defined $_[1]->{ErrorMsg}) {
                                     $_[1]->{ErrorMsg} = $_[2];} },
    "^(.+:\\d+: (Error|Unimplemented|Bug):.+)\$" 
                     => sub { if(! defined $_[1]->{ErrorMsg}) {
                                       $_[1]->{ErrorMsg} = $_[2];} },
    "^(.+: fatal error.+)\$" => sub { if(! defined $_[1]->{ErrorMsg}) {
                                         $_[1]->{ErrorMsg} = $_[2];} },
    "^stackdump: Dumping stack trace" => 
                   sub { if(! defined $_[1]->{ErrorMsg}) {
                         $_[1]->{ErrorMsg} = $_[2];} },


    "^user\\s+(\\d+)m([\\d.]+)s"
              => sub { $_[1]->{RUN} = 60 * $_[2] + $_[3]; },

    "^TOTAL\\s+([\\d.]+) s" => sub { $_[1]->{CURE} = $_[2]; },
    );

                                         
# Add a test.
# command is the base name of the tests + space separated arguments
# extrargs are passed on the command line for each test
# fields must be fields to be added to the newly created tests
sub addTest {
    my($command, %extrafields) = @_;

    my $self = $main::globalTEST;
    my ($name, $extraargs) = 
        ($command =~ /^(\S+) ?(.*)$/);     # name is first word

    my $theargs = $self->testCommandExtras($extraargs);

    my %patterns = %commonerrors;
    my $kind;

    my $tst =
        $self->newTest(Name => $name,
                       Dir => ".",
                       Cmd => "$make " . $name . $theargs,
                       Group => [ ],
                       Patterns => \%patterns);
    # Add the extra fields
    my $key;
    foreach $key (keys %extrafields) {
        $tst->{$key} = $extrafields{$key};
    }
    return $tst;
}
sub addTestFail {
    my($command, $failpattern) = @_;
    addTest($command, MustFail => $failpattern);
}




sub addBadComment {
    my($name, $comm) = @_;
    my $self = $main::globalTEST;
    $self->addComment($name, $comm);
    $self->addGroups($name, "bad");
}




sub addToGroup {
    my ($name, @groups) = @_;
    my $self = $main::globalTEST;
    $self->addGroups($name, @groups);
}


# Start with a few tests that must be run first
$TEST->newTest(
    Name => "!inittests0",
    Dir => "..",
    Cmd => "$make setup",
    Group => ['ALWAYS']);
$TEST->newTest(
    Name => "!inittests2",
    Dir => "..",
    Cmd => "$make setup _GNUCC=1",
    Group => ['ALWAYS']);


# build the documentation, to make sure that it still builds
$TEST->newTest(
    Name => "doc",
    Dir => "..",
    Cmd => "$make doc",
    Group => ["doc"]);
    
# Now add tests
addTest("testrun/const-array-init WARNINGS_ARE_ERRORS=1");
addTest("testrun/const-struct-init WARNINGS_ARE_ERRORS=1");
addTest("test/const-struct-init WARNINGS_ARE_ERRORS=1");
addTest("test/warnings-noreturn WARNINGS_ARE_ERRORS=1");
addTest("testrun/warnings-unused-label WARNINGS_ARE_ERRORS=1");
addBadComment("testrun/warnings-unused-label", 
	      "Minor. We don't do a good enough job at eliminating unused labels");
addTest("test/warnings-cast WARNINGS_ARE_ERRORS=1");
addTest("testrun/castincr WARNINGS_ARE_ERRORS=1");

addTest("test/apachebits");
addTest("testrun/apachebuf");

addTest("testrun/apachefptr");
addTest("testrun/asm1 _GNUCC=1");
addTest("test/asm2 _GNUCC=1");
addTest("test/asm3 _GNUCC=1");
addTest("test/asm4 _GNUCC=1");
addBadComment("test/asm4", "Limitation. See testrun/const1.");
addTest("testobj/asm5 _GNUCC=1");

addTest("testrun/offsetof");
addTest("testrun/offsetof1");
addTest("testrun/offsetof2");
addTest("testrun/offsetof3");
addTest("testrun/question");
addTest("testrun/question2");
addTest("test/argcast");
addBadComment("test/argcast", 
	      "Notbug. CIL bases type for implicit functions based on first call's argument.");
addTest("test/array1");
addTest("test/array2");
addTest("testrun/array_varsize");
addTest("testrun/array_formal");
addTest("testrun/formalscope");
addTest("test/matrix");
addTest("runall/switch");
addTest("testrun/strloop");
addTest("testrun/strloop3");
addTest("testrun/percentm");
addTest("testrun/percent400");
addTest("testrun/caserange _GNUCC=1");
addTest("test/attr");
addTest("test/attr2 _GNUCC=1");
addTest("test/attr3 _GNUCC=1");
addTest("testrun/attr4 _GNUCC=1");
addTest("testrun/attr5_GNUCC=1");
addTest("test/attr6 _GNUCC=1");
addTest("test/attr7 _GNUCC=1");
addTest("test/attr8 _GNUCC=1");
addTest("test/attr9 _GNUCC=1 WARNINGS_ARE_ERRORS=1");
addTest("test/attr10 _GNUCC=1");
addTest("test/attr11 _GNUCC=1");
addTest("test/attr12 _GNUCC=1");
addTest("test/attr13 _GNUCC=1");
addTest("testrun/packed _GNUCC=1 WARNINGS_ARE_ERRORS=1");
addTest("test/packed2 _GNUCC=1");
addTest("test/bitfield");
addTest("testrun/bitfield3");
     
addTest("testrun/bitfield2");
addTest("testrun/call2 ");
addTest("test/cast1");
addTest("test/cast2");
addTest("test/cast4 _GNUCC=1");
addTest("testrun/cast8 ");
addTest("test/constprop");
addTest("testrun/const1 _GNUCC=1");
addBadComment("testrun/const1", "Limitation. CIL can't handle large 64-bit unsigned constants.");
addTest("testrun/const2 ");
addTest("testrun/const3 ");
addTest("testrun/const4 _GNUCC=1");
addTest("testrun/const5 _GNUCC=1");
addTest("testrun/const6 ");
addTest("test/const7 ");
addTest("testrun/const8 ");
addTest("test/const9 ");
addTest("testrun/const10 ");
addTest("testrun/const11 ");
addTest("testrun/const12 ");
addTest("test/const13 WARNINGS_ARE_ERRORS=1");
addBadComment("test/const13", "Minor. Const warnings from generated code - need more casts.");
addTest("test/const14");
addBadComment("test/const14", "Bug. Missing cast to result type when short-cutting expressions to 0.");
addTest("test/deref _GNUCC=1");
addTest("test_i/empty");
addTest("test/enum");
addTest("testrun/enum2");
addTest("test/func");
addTest("test/funcarg ");
addBadComment("test/funcarg", 
                        "Bug. In parser (argument of function type)");

addTest("testrun/func2");
addTest("testrun/func3");
addTest("testrun/func4");
addTest("test/func10 ");
addBadComment("test/func10", 
                     "Bug. Cannot parse some strange K&R function definition");
addTest("test/globals");
addTest("test/globals2 ");
addBadComment("test/globals2", "Bug. we print array size expressions that refer to variables that haven't been defined yet.");
addTest("testrun/float");
addTest("testrun/float2 ");
addTest("test/huff1");
addTest("testrun/init");
addTest("testrun/init1");
addTest("testrun/init2 _GNUCC=1");
addTest("testrun/init3 _GNUCC=1");
addTest("testrun/init4 _GNUCC=1");
addTest("testrun/init5 _GNUCC=1");
addTest("testrun/init6 ");
addTest("test/init8 _GNUCC=1");
addTest("testrun/init9 _GNUCC=1");
addTest("testrun/init9 _GNUCC=1");
addTest("testrun/init10 _GNUCC=1");
addTest("testrun/init11 _GNUCC=1");
addTest("testrun/init12 _GNUCC=1");
addTest("testrun/init13 _GNUCC=1");
addTest("testrun/init14 _GNUCC=1");
addTest("testrun/init15 _GNUCC=1");
addTest("testrun/init16 ");
addTest("testrun/init17 ");
addTest("testrun/init18 ");
addBadComment("testrun/init18", "Bug. Outstanding since 1.3.6 at least");
addTest("testrun/init19 WARNINGS_ARE_ERRORS=1");
addTest("testrun/init20 _GNUCC=1");
addTest("testrun/init21 _GNUCC=1");
addTest("testrun/init22 ");
addTest("test/array-size-trick ");
addTest("testrun/logical ");
addTest("testrun/cond1 _GNUCC=1");
addTest("testrun/cond2 _GNUCC=1");
addTest("testrun/initial _GNUCC=1");
addTest("testrun/inline1 _GNUCC=1");
addBadComment("testrun/inline1", "Notbug. CIL now matches gcc's new behavior for extern inline, this test checks for the old behavior.");
addTest("testrun/inline2 _GNUCC=1");
addTest("test/inline3 _GNUCC=1");
addTest("test/decl2 _GNUCC=1");
addBadComment("test/decl2", 
	      "Bug. An old-style argument type should go through the default type conversion before being added to the function's type.");
addTest("test/jmp_buf");
addTest("test/linux_atomic _GNUCC=1");
addTest("testrun/linux_signal _GNUCC=1");
addTest("test/li");
addTest("test_i/lineno");
addTest("test/list");
addTest("testrun/localinit ");

addTest('testrun/longBlock', '');
addTest("testrun/perror");
addTest("testrun/perror1");
addTest("test/pure");
addTest("testrun/post-assign ");
addBadComment("testrun/post-assign", 
                        "Minor. CIL does not have the same evaluation order for ++ as gcc");
addTest("test/printf ");
addTest("test/printf_const ");
addTest("testrun/printf2");
addTest("test/unimplemented");
addTest("testrun/vararg1");
addTest("testrun/vararg2");
addTest("testrun/vararg3");
addTest("testrun/vararg4");
if($win32) {
  addTest("testrun/vararg11 _MSVC=1");
}
addTest("testrun/varargauto1");
addTest("testrun/vararg5 _GNUCC=1");
addTest("testrun/vararg6");
addTest("test/vararg7 _GNUCC=1");
addTest("testrun/va-arg-1 _GNUCC=1");
addTest("testrun/va-arg-2 _GNUCC=1");
addTest("testrun/va-arg-7 _GNUCC=1");
addTest("test-bad/arrsize ");
addTest("testrun/comma1 _GNUCC=1");
addTest("test/retval");
addTest("testrun/static ");
addTest("test/static1");
addTest("testrun/static2 ");
addTest("test/strcpy");
addTest("test/struct_init");
addTest("test/structassign");
addTest("testrun/align1 _GNUCC=1");
addTest("testrun/align2 _GNUCC=1 EXTRAARGS=-O2");
addTest("test/align3 _GNUCC=1");
addTest("test/tags");
addTest("test/task _GNUCC=1");
addTest("test/power1");
addTest("testrun/scope1");
addTest("test/scope2");
addTest("test/scope3");
addBadComment("test/scope3", "Notbug. This failure is ok - enum's may be represented by a type other than int, even though enum constants are of type int...");
addTest("test/scope4");
addTest("testrun/scope5 _GNUCC=1");
addTest("testrun/scope6");
addTest("testrun/scope8");
addTest("testrun/scope9 ");
addTest("testrun/scope10 ");
addTest("testrun/scope11 ");
addTest("test/voidstar");
addTest("testrun/memcpy1");

addTest("test/noreturn ");
                

addTest("testrun/label1");
addTest("testrun/label2");
addTest("testrun/label3");
addTest("testrun/label4 _GNUCC=1");
addTest("test/label5");
addTest("testrun/label6");
addTest("test/label7");
addTest("test/label8");
addTest("test/label9 EXTRAARGS=--domakeCFG");
addTest("testrun/wchar1");
addTest("testrun/wchar2");
addTest("testrun/wchar3");
addTest("testrun/wchar4");
addTest("testrun/wchar5 ");
addTest("testrun/wchar6"); 
addTest("testrun/wchar7"); 
addTest("testrun/escapes");
addTest("test-bad1/wchar-bad ");
addTest("testrun/addrof3 _GNUCC=1");
addTest("testrun/lval1 _GNUCC=1");
#MIA: addTest("test/bind2 EXTRAARGS=--allowInlineAssembly");
#addToGroup("test/bind2", "slow");
addTest("testrun/decl1 _GNUCC=1");
addTest("testrun/addr-array");
addTest("combine1 ");
addTest("combine2 ");
addTest("combine3 ");
addTest("combine5 ");
addTest("combine6 ");
addTest("combine8 ");
addTestFail("combine9 ", "Incompatible declaration for g");
addTest("combine10 ");
addTest("combine11 ");
addTest("combine12 ");
addTest("combine13 ");
addTest("combine14 ");
addTest("combine15 ");
addTest("combine16 ");
addTest("combine17 ");
addTest("combine18 ");
addTest("combine20 ");
addTest("combine21 ");
addTest("combine22 ");
addBadComment("combine22", "Bug. Outstanding since 1.3.6 at least");
addTest("combinealias ");
addTest("combinelibrik ");
addTest("combineenum1 ");
addTest("combineenum2 ");
addTest("combineenum3 ");
addTest("combine_init ");
addTest("combineinline1 ");
addBadComment("combineinline1", "Bug. Outstanding since 1.3.6 at least");
addTest("combineinline2 ");
addTest("combineinline3 ");
addBadComment("combineinline3", "Bug. Outstanding since 1.3.6 at least");
addTest("combineinline4 ");
addBadComment("combineinline4", "Bug. Outstanding since 1.3.6 at least");
addTest("combineinline6 ");
addTest("combinestruct1 ");
addTest("mixedcomb ");
addTest("testrun/math1 ");
addTest("test/linuxcombine1_1 ");

addTest("arcombine _GNUCC=1");
addTest("testrun/funptr1");
addTest("testrun/typespec1 _GNUCC=1");
addBadComment("testrun/typespec1", 
                        "Notbug. GCC 4 no longer allows this, so the error is fine.");
addTest("testrun/returnvoid ");
addTest("testrun/returnvoid1 ");
addTest("testrun/return1 ");
addTest("testrun/for1 ");
addTest("testrun/void _GNUCC=1");
addTest("test/voidtypedef ");
addTest("testrun/wrongnumargs ");
addBadComment("testrun/wrongnumargs", 
                        "Notbug. Should fail since we don't pad argument lists");
addTest("test/restrict EXTRAARGS=-std=c9x _GNUCC=1");
addTest("test/restrict1 _GNUCC=1");
addTest("testrun/rmtmps1 ");
addTest("testrun/rmtmps2 _GNUCC=1");
addTest("test/proto1 ");
addBadComment("test/proto1", 
	      "Bug. CIL doesn't like pointers to old-style functions...");
addTest("test/proto2 ");
addBadComment("test/proto2", 
                        "Bug. In parser (precedences)");
addTest("testrun/struct1 ");
addTest("testrun/voidarg ");
addTest("testrun/union2 ");
addTest("testrun/union3 ");
addTest("test/union5 ");
addTest("runall/extinline ");

addTest("testrun/rmtmps-attr ");
addBadComment("testrun/rmtmps-attr", 
                        "Bug. A limitation of our support for attributes");
 
addTest("testrun/vsp");

addTest("test/cpp-2 ");
addBadComment("test/cpp-2", 
                        "Bug. In parser (empty pragmas)");
addTest("test/cpp-3 _GNUCC=1");

addTest("testrungcc/enum3 _GNUCC=1");
addTest("testrungcc/enum3a _GNUCC=1");
addTest("testrungcc/enum3b _GNUCC=1");
addTest("testrungcc/enum3c _GNUCC=1");
addBadComment("testrungcc/enum3c", 
                        "Limitation. CIL constant folder doesn't consider x << y constant if y is strange (negative or bigger than #bits in x's type)");
addTest("testrungcc/enum3d _GNUCC=1");
addTest("testrungcc/enum3e _GNUCC=1");
addTest("testrungcc/enum3f _GNUCC=1");
addTest("testrungcc/enum3g _GNUCC=1");
addTest("testrungcc/enum3h _GNUCC=1");
addTest("testrungcc/enum3i _GNUCC=1");
addTest("testrungcc/enum3j _GNUCC=1");
addTest("testrungcc/enum3k _GNUCC=1");
addTest("testrungcc/enum3l _GNUCC=1");


if($win32) {
    addTest("testrun/extern_init _MSVC=1");   
    addTest("testrun/msvc2 _MSVC=1");
    addTest("testrun/msvc3 _MSVC=1");
    addTest("testrun/msvc4 _MSVC=1");
    addTest("testrun/msvc6 _MSVC=1");
    addTest("testrun/msvc7 _MSVC=1");
    addTest("testrun/msvc8 _MSVC=1");
    addTest("testrun/msvc9 _MSVC=1");

    addTest("test-bad/try1 _MSVC=1");
}
addTest("testrun/msvc1 ");
addTest("testrun/msvc5 ");

addTest("testrun/extern1 ");

addTest("test/duplicate ");

addTest("testrun/simon6");
    
addTest("testrun/stringsize");
addTest("testrun/min ");



addTest("test/simplify_structs1 USECILLY=1 EXTRAARGS=--dosimplify");
addTest("testrun/simplify_structs2 USECILLY=1 EXTRAARGS=--dosimplify");

addTest("test/tempname EXTRAARGS=--dosimplify");

addTest("testrun/typeof1 ");
addTest("testrun/semicolon _GNUCC=1");

addTest("merge-ar ");



addTest("testrun/sizeof1");
addTest("testrun/sizeof2");
addTest("runall/sizeof3");
addTest("test/outofmem ");
addTest("testrun/builtin ");
addTest("test/builtin2 ");
addTest("testrun/builtin3 ");
addTest("testrun/builtin_choose_expr");
addTest("testrun/builtin4 ");
addTest("test/builtin5 ");
addTest("test/sync-1 _GNUCC=1");
addTest("test/sync-2 _GNUCC=1");
addTest("test/sync-3 _GNUCC=1");
addTest("testrun/comparisons");
addTest("testrun/assign");
    



# self-contained tests of specific things which had problems before
addTest("scott/multiplestatics");
addTest("scott/partialbracket");
addTest("scott/enuminit");

addTest("scott/gimpdouble");
addTest("scott/struct_cs");


addTest("scott-nogcc/bogus_redef");
addTest("scott/s59");
addTest("scott/putc $gcc");
addTest("scott/lexnum");
addTest("scott/ctype");


# function pointers don't work with inferred wildness
addTest("scott/funcptr");

# transparent unions are a problem for network apps
addTest("scott/transpunion $gcc");
addTest("scott/sockaddr $gcc");

# misc...
addTest("scott/constdecl");
addTest("scott/oldstyle");
addTest("scott/typeof $gcc");
addTest("scott/asmfndecl $gcc");
addBadComment("scott/asmfndecl", "Notbug. Not a bug if fails on a non-Linux machine ;-)");
addTest("scott/open $gcc");
addTest("scott/constfold");
addTest("scott/mode_sizes $gcc");       # mode(__QI__) stuff
addTest("scott-nolink/brlock $gcc");
addTest("scott/regparm0 $gcc");         # this works, unfortunately..
addBadComment("scott/regparm0", "Bug. Also gcc bug. regparm attribute not handled well, compounded by gcc treating multiple regparm attributes inconsistently between function declarations and definitions.");
addTest("scott/unscomp");               # kernel/fs/buffer.c
addTest("scott/thing");

# current problematic test cases
addTest("mergeinline");
addTest("scott/uninit_tmp");
addTest("combine_samefn");
addBadComment("combine_samefn", "Bug. Outstanding since 1.3.6 at least");
addTest("combine_node_alloc");
addBadComment("combine_node_alloc", "Bug. Outstanding since 1.3.6 at least");
addTest("combine_sbump");
addTest("combine_sbumpB");
addTest("combine_sbumpB MERGEINLINES=1");
addTest("combine_allocate");
addTest("combine_allocate MERGEINLINES=1");
addTest("combine_theFunc");
addTest("combine_theFunc MERGEINLINES=1");
addTest("combine_syserr");
addTest("combine_syserr MERGEINLINES=1");
addTest("combine_copyptrs WARNINGS_ARE_ERRORS=1");
addTest("combine_copyptrs WARNINGS_ARE_ERRORS=1 MERGEINLINES=1");

# tests of things implemented for EDG compatibility
addTest("mergestruct");

# a few things that should fail
addTest("test-bad/trivial-tb");
addTest("runall/runall_misc");


# simple test of combiner
addTest("comb $gcc");

# test combiner's ability to detect inconsistency
addTest("baddef");


# does not work: complains of many incompatible type redefinitions
#runTest $make apache/rewrite

addTest("test/init");
addTest("test/initial");
addTest("test/jmp_buf");
addTest("test/static");


# more random stuff
addTest("scott-nogcc/funcname $gcc");
addTest("scott/litstruct $gcc");
addTest("scott/main $gcc");
addTest("scott/globalprob $gcc");
addBadComment("scott/globalprob", "Notbug. Not a bug if fails on a non-Linux machine ;-)");
addTest("scott/bisonerror $gcc");
addTest("scott/cmpzero");
addTest("scott/kernel1 $gcc");
addTest("scott/kernel2 $gcc");
addTest("scott/xcheckers $gcc");
addTest("scott/memberofptr $gcc");
addTest("scott/invalredef $gcc");
addTest("scott/invalredef2 $gcc");
addTest("scott/errorinfn");
addTest("scott/unionassign");
addTest("scott/structattr");
addTest("scott/neg64");
addTest("testrun/arrayinitsize");
addTest("test-bad/enuminit2");
addTest("scott/volatilestruct");
addTest("scott/sizeofchar");
addTest("scott/initedextern");
addTest("scott/arrayinit");
addTest("runall/structattr2");
addTest("scott/structattr3");
addTest("scott/enumerator_sizeof");
addTest("testrun/decl_mix_stmt");
addTest("scott/enumattr");
addTest("runall/alpha");
addTest("testrun/blockattr2");
addTest("testrun/extinline2");
addTest("test/extinline3");
addTest("testrun/bool");
addTest("test/va_arg_pack");
addTest("testrun/compound1");
addBadComment("testrun/compound1", "Notbug. Undefined behavior (probably).");
addTest("testrun/compound2");


# ---------------- c-torture -------------
## if we have the c-torture tests add them
## But only if the ctorture group was specfied
my $ctorture = '/usr/local/src/gcc/gcc/testsuite/gcc.c-torture';
if(-d $ctorture && 
   defined $TEST->{option}->{group} &&
    grep { $_ eq 'ctorture'} @{$TEST->{option}->{group}}) {
    
    # Omit some tests because they use __complex__
    my @omit = ('compile/20000804-1', 'compile/20001222-1', 'compile/941019-1',
                'compile/981223-1', 'compile/991213-1', 'compile/20010605-2',
                'compile/960512-1', 'compile/complex-1', 
                'compile/complex-2', 'compile/complex-4', 
                'compile/complex-5', 'execute/complex-2', 'execute/complex-5',
                'execute/960512-1', 'execute/complex-4', 
                'execute/complex-1', 'execute/20010605-2');

    # Also omit those with inner functions
    push @omit, 
    ('compile/951116-1', 'compile/920415-1',
     'execute/920415-1', 'compile/20010605-1', 
     'execute/20010605-1', 'compile/20011023-1',
     'compile/20010903-2', 'execute/comp-goto-2', 'execute/nestfunc-2',
     'execute/921215-1', 'execute/920428-2', 'execute/921017-1',
     'execute/nest-stdar-1', 'execute/nestfunc-3', 'execute/920501-7', 
     'execute/920721-4', 'execute/920612-2', 'execute/20010209', 
     'execute/931002-1', 'execute/nestfunc-1', 'execute/20000822-1',
     'compile/930506-2', 'execute/20010209-1');

    # Read the compile tests 
   my @tortures;
   foreach my $tortdir ('compile', 'execute', 'compat') { 
       @tortures = 
           map { $_ =~ m|$ctorture/$tortdir/(.+)\.c|; $1 } 
                 (glob "$ctorture/$tortdir/*.c");
       # Remove those that were produced in previous runs
       @tortures = grep { $_ !~ m|cil$| } @tortures;
       # Remove those that we know should fail
       @tortures = grep { my $t = "$tortdir/$_"; 
                          ! grep { $_ =~ m|$t|} @omit } @tortures;
       foreach my $tst (@tortures) {
           addTest("tort/$tortdir/$tst _GNUCC=1"); 
           $TEST->addGroups("tort/$tortdir/$tst", 'ctorture');
       }
   }
}


## We add here a mechanism for adding new tests
if(defined $ENV{CILEXTRATESTS}) {
    require $ENV{CILEXTRATESTS};
}

# print Dumper($TEST);


# Now invoke it
$TEST->doit();

# print Dumper($TEST);

exit(0);


###
###
###
### Specialize RegTest
###
package CilRegTest;

use strict;
# use Data::Dumper;

BEGIN {
    use RegTest;
    @CilRegTest::ISA = qw(RegTest);        # Inherit from RegTest
}

# The constructor
sub new {
    my $proto = shift;
    my $class = ref($proto) || $proto;
    my $self = $class->SUPER::new(@_);

    return $self;
}

# Special command line options
sub extraOptions {
    my($self) = @_;
    my @supopt = $self->SUPER::extraOptions();
    return (
        @supopt,
        "--cildebug!",
        "--noremake!", 
            );
}


sub extraHelpMessage {
    my($self) = @_;
    
    my ($scriptname, $extra) = $self->SUPER::extraHelpMessage();
    return ("testcil",
            $extra . << "EOF");

Additional arguments for SafeC test harness
  --cildebug           Use the debug versions of everything (default is false)
  --noremake           Does not try to remake the executable before each test.
                       (so that you can modify the sources while the test 
                       is running)
  Default log file is safec.log
EOF
}

sub errorHeading {
    my($self, $err) = @_;
    return "Not executed" if $err == -1;
    return "Success" if $err == 0;
    return "Preprocessor error" if $err == 1000;
    return "Parse error" if $err == 1001;
    return "Cabs2cil error" if $err == 1002;
    return "Compilation error" if $err == 1007;
    return "Execution error" if $err == 1008;
    return $self->SUPER::errorHeading($err);
}

sub startParsingLog {
    my($self, $tst) = @_;
    $tst->{instage} = 1000;
    $tst->{ErrorCode} = 0;
}


sub availableParameters {
    my($self) = @_;
    return %::availpars;
}


# given the current options configuration, return a string of
# additional 'make' arguments to append to test commands
sub testCommandExtras {
    my ($self, $extraargs) = @_;

    # (sm: pulled this out of addTests so I could write my own addTests)
    my $theargs = defined($self->{option}->{cildebug})
        ? " " : " RELEASE=1 ";
    $theargs .= " $extraargs ";
    if(defined $self->{option}->{noremake}) {
        $theargs .= " NOREMAKE=1";
    }
    # Turn on the verbose flag
    $theargs .= " STATS=1 PRINTSTAGES=1 ";
    # Turn on the strings
    # $theargs .= " EXTRAARGS=--useStrings ";

    return $theargs;
}



# ensure uniqueness of names (I don't like using these names to
# name tests.. regrtest used numbers.. oh well)
sub uniqueName {
  my ($self, $name) = @_;

  if (!$self->testExists($name)) {
    return $name;   # already unique
  }
  else {
    my $ct = 2;
    while ($self->testExists($name . $ct)) {
      $ct++;
    }
    return $name . $ct;
  }
}


1;
