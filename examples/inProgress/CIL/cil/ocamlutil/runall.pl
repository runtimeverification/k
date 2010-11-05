#!/bin/perl

use strict;
use File::Basename;

# usage runall.pl filename
#      See below for the environment variables that control the execution
#
#
# The file is expected to contain the code for the tests.
#
# The test file is scanned for lines that contain some keywords. In 
# all cases the rest of the line following the keywords must be a test
# specification, of the form:
#
#  TestSpec ::= [testname] [: (error|success)[(=|~) "message"]]
#
# "testname" is the (optional) name of the test. If it is missing
#   then a fresh new numeric name is made up. 
#
# If this specification is not the first for the given test name then the rest
# of the line may be empty. Otherwise there must be at least [: error] or [:
# success], to say whether this test should fail or should succeed. 
#
# Both for success and for failure you can define some text that must appear 
# in the output of the test (with the = specifier), or a Perl regexp that must
# appear in the output (with the ~ specifier). 

#
# In a first pass, the file is scanned to collect a list of tests.
# If there are no tests defined in the file, then we assume a default line
#    TESTDEF default : success
# This actually means that 
#
# Then for each test we process the file and we comment out some lines based
# on the keywords that appear in the file:
#
#  TESTDEF TestSpec  - defines a test, must appear alone on a line
#  DROP TestSpec     - this line is dropped ONLY during that test
#  KEEP TestSpec     - this line is kept ONLY during that test
#  IFTEST TestSpec   - keeps a whole bunch of lines ONLY for this test.
#                      IFTEST, ELSE and ENDIF must appear alone on a line
#   ...
#  [ ELSE
#    ...
#    ENDIF ]
#
#  IFNTEST ...       - same syntax as IFTEST. 
#
#  The lines containing TESTDEF, IFTEST, ELSE, ENDIF will always 
#  be commented. The DROP and the KEEP keywords must appear after a comment
#  character. 
#
#
#  EXAMPLES
#
#  ======== foo1.c ======
#  int main() { return 0; }
#  
#  ==
#      Only one test, called "default" will be executed and expected to
#      succeed
#
#  ======= foo2.c ======
#  int main() { 
#      return 1; // KEEP : error
#      return 0; // KEEP : success
#  }
#
#  ==
#    Two tests are executed, one with each version of the return. The test
#    that contains "return 1" is expected to fail, while the other is 
#    expected to succeed
#

#
#  The result of processing the file for each test is obtained from the 
#  directory and base names of the file along with "-tmp" followed by the 
#  original extension. Thus, for "foo/test.s" we get "foo/test-tmp.s".
#
#  If the environment variable RUNONLY is set to tst, then only the test named
#  tst is run.
#
#  If the environment variable KEEPGOING is set, then we continue after
#  errors.
#
#  If the environment variable COMMENT is set, then this string is used to
#  comment out a line. Otherwise, the lines that must be dropped are not
#  printed.
#
#  If the environment variable KEEP is set, then we do not delete the 
#  files that are generated.
#
#  The COMMAND variable must contain the command to run for each test. The 
#  following substitutions are done: 
#   __FILE__ with the name of the transformed file
#  __BASENAME__ with the basename (no directory, no extension)
#  __EXT__ with the extension
#  __DIR__ with the directory
#
#  If none of the above substitutions can be performed, then the 
#  name of the file is appended to the command.
#
#

my %testnames;

my ($base, $dir, $ext) = fileparse($ARGV[0], qr{\.[^.]+});

my $outbasename = "$base-tmp";
my $outext = $ext;
my $outdir = $dir;
my $outfile = "$dir$base-tmp$ext";

my $action = 'COLLECT';

my $countFreshName;

my $hadErrors = 0;

my $debug = 1;

# Collect the test cases
&scanTestFile("");

$action = 'PROCESS';

my $countTests = 0;

if(defined $ENV{'RUNONLY'}) {
    if(! defined $testnames{$ENV{'RUNONLY'}}) {
        die "Test $ENV{'RUNONLY'} does not exist";
    }
    &runOneTest($ENV{'RUNONLY'});
} else {
    # Now run over all tests
    foreach my $t (sort (keys %testnames)) {
        &runOneTest($t);
    }
}
if(not defined $ENV{'KEEP'}) { 
    unlink $outfile;
}
if($hadErrors) { 
    print "There were errors!\n";
    exit 1;
} else {
    print "All $countTests tests were successful!\n";
    exit 0;
}
1;


##############################

sub parseTestDef {
    my ($text, $line) = @_;
    my ($name, $success, $msg, $msgpattern);

    # All the way to : is the name of the test
    if($text !~ m|^([^:]+):(.*)$|) {
        # There is no :. All of it is the name of the test. Trim spaces
        ($name) = ($text =~ m|^\s*(\S.*)$|);
        ($name) = ($name =~ m|^(.*\S)\s*$|);
        if($name eq "") {
            die "Test definition with no name and no : error or : success";
        }
        if(! defined $testnames{$name}) {
            die "Unknown test";
        } 
        return $name;
    } else {
        # We have a :  This is a test definition
        my $rest = $2;
        ($name) = ($1 =~ m|^\s*(\S.*)$|);
        ($name) = ($name =~ m|^(.*\S)\s*$|);
        if($name eq "") {
            $name = $countFreshName ++;
        }
        # See if this is success
        if($rest !~ m|^\s*(error\|success)(.*)$|) {
            die "After success or error there must be =\n";
        }
        $success = ($1 eq "success") ? 1 : 0;
        $rest = $2;

        # See if there is a message. Must be at least two chars long
        if($rest =~ m|^\s*(=\|~)\s*(\S.*\S)\s*$|) {
            $msg = $2;
            $msgpattern = ($1 eq "~");
        } else {
            if($rest =~ m|^\s*$|) {
                $msg = "";
                $msgpattern = 0;
            } else {
                die ("After " . ($success ? "\"success\"" : "\"error\"") .
                     " there must be nothing of = ...");
            }
        }
            

        # We have found a test
        if($action eq 'COLLECT') {
            if(defined $testnames{$name} &&
               $testnames{$name}->{SUCCESS} != $success) {
                die "Test $name is defined both success and error";
            }
            if(defined $testnames{$name} &&
               $testnames{$name}->{'MSG'} ne "" && 
               $msg ne "") {
                warn "Ignoring duplicate message for $name: $msg";
            } else {
                print "Found test $name with msg:$msg\n";
                $testnames{$name} = { SUCCESS => $success,
                                      LINE => $line,
                                      MSG => $msg,
                                      MSGPATTERN => $msgpattern };
            }
        }
        return $name;
    }
}

# Populate the test data
sub scanTestFile {
    my($current) = @_;

    $countFreshName = 0;
    open(IN, "<$ARGV[0]") || die "Cannot open file $ARGV[0]";

    # We keep track of the IF scopes we are in. We keep a stack of scopes,
    # starting with the global scope. For each scope on the stack we keep a
    # boolean, saying whether the scope is positive or negative. 
    my @ifenv = (1); # We enclose everything in a positive global scope

    # This variable is the && of all entries in ifenv
    my $keep = 1;

    my $COMMENT = "//";
    if (defined $ENV{'COMMENT'}) {
        $COMMENT = $ENV{'COMMENT'};
    }
    my $line = 0;
    while(<IN>) {
        $line ++;
        my $name; 

        my $comment = 0;

        my $linename = "";

        # Look first at the test descriptions
        # Set $comment if we want to comment this line
        if($_ =~ m|^\s*TESTDEF(.*)$|) {
            $name = &parseTestDef($1, $line);
            $comment = 1;

        } elsif($_ =~ m|$COMMENT\s*DROP(.*)$|) {
            $name = &parseTestDef($1, $line);
            if($name eq $current) { $comment = 1; }
            $linename = "DROP($name)";

        } elsif($_ =~ m|$COMMENT\s*KEEP(.*)$|) {
            $name = &parseTestDef($1, $line);
            if($name ne $current) { $comment = 1; }
            $linename = "KEEP($name)";

        } elsif($_ =~ m|^\s*IFTEST(.*)$|) {
            $name = &parseTestDef($1, $line);
            $linename = "IFTEST($name)";
            # Push on the stack
            unshift @ifenv, ($name eq $current ? 1 : 0);
            $keep = &allTrue(@ifenv);
            $comment = 1;

        } elsif($_ =~ m|^\s*IFNTEST(.*)$|) {
            $name = &parseTestDef($1, $line);
            $linename = "IFNTEST($name)";
            unshift @ifenv, ($name ne $current ? 1 : 0);
            $keep = &allTrue(@ifenv);
            $comment = 1;

        } elsif($_ =~ m|^\s*ELSE\s*$|) {
            # Stack must have at least 2 elements
            if($#ifenv < 1) { die "Found ELSE without IF"; }
            $linename = "ELSE";
            $ifenv[0] = ($ifenv[0] ? 0 : 1);
            $keep = &allTrue(@ifenv);
            $comment = 1;

        } elsif($_ =~ m|^\s*ENDIF\s*$|) {
            # Stack must have at least 2 elements
            if($#ifenv < 1) { die "Found ENDIF without IF"; }
            $linename = "ENDIF";
            shift @ifenv;
            $keep = &allTrue(@ifenv);
            $comment = 1;
        }

        # We are done if collecting
        if($action ne 'PROCESS') { next; }

        my $keep_this_line = $comment ? 0 : $keep;
        if($debug && $linename ne "") {
            if($linename =~ m|^KEEP| ||
               $linename =~ m|^DROP|) {
               print "$line: $linename: keep=", ($comment ? 0 : 1), "\n";
            } else {
               print "$line: $linename: keep=$keep, env = ", join(',', @ifenv), "\n";
           }
        }
        if($comment || ! $keep) {
            if(defined $ENV{'COMMENT'}) {
                print OUT $ENV{'COMMENT'};
                print OUT " ";
                print OUT $_;
            } else {
                print OUT "\n";
            }
        } else {
            print OUT $_;
        }
    }

    if(0 == keys %testnames) {
        print "There are no tests defined in the file. Assume a success test\n";
        &parseTestDef("default : success", -1);
        
    }
}

sub allTrue {
    my $res = 1;
    while(@_) {
        if(! (shift @_)) {
            $res = 0;
        }
    }
    return $res;
}


sub runOneTest {
    my($t) = @_;
    my $ti = $testnames{$t};

    $countTests ++;

    print "\n********* $base: Running test $t from line $ti->{LINE}\n";
    if($debug) {
        print "Test $t:\n\tSUCCESS => $ti->{SUCCESS}\n\tLINE => $ti->{LINE}\n\tMSG => $ti->{MSG},\n\tMSGPATTERN => $ti->{MSGPATTERN}\n";
    }
    open(OUT, ">$outfile\n") 
        || die "Cannot write $outfile";
    &scanTestFile($t);
    close(OUT) || die "Cannot close file $outfile";
    # Now we run the command
    if(! defined $ENV{COMMAND}) {
        die "You forgot to set the COMMAND";
    }
    my $command = $ENV{COMMAND};
    # Substitute __FILE__ with the current file
    if($command =~ m|__FILE__|) {
        $command =~ s|__FILE__|$outfile|g;
    }
    if($command =~ m|__DIR__|) { 
        $command =~ s|__DIR__|$outdir|g;
    } 
    if($command =~ m|__BASENAME__|) { 
        $command =~ s|__BASENAME__|$outbasename|g;
    }
    if($command =~ m|__EXT__|) { 
        $command =~ s|__EXT__|$outext|g;
    }
    if($command eq $ENV{COMMAND}) {
        $command .= " $outfile";
    }
    print "$command\n";
    my $msgfile = "runall_out";
    my $code = system("($command) >$msgfile 2>&1");
    open(MSG, "<$msgfile") || die "Cannot read $msgfile";
    my @msgs = <MSG>;
    close(MSG) || die "Cannot close $msgfile";
    print @msgs;
    unlink $msgfile;
    if($debug) { 
        print "Test $t returned with code $code. Expected ", 
        ($ti->{SUCCESS} ? "success" : "failure", "\n");
    }
            
    if(($code == 0) != $ti->{SUCCESS}) {
        if($code == 0) {
            warn "Test case $t (line $ti->{LINE}) succeeds and it is supposed to fail";
        } else {
            warn "Test case $t (line $ti->{LINE}) fails and it is supposed to succeed";
        } 
        $hadErrors = 1;
        if(! defined($ENV{KEEPGOING})) {
            die "";
        } 
    } else {
        # Now we check the output for the message
        if($ti->{MSG} ne "") {
            # See if the message occurs
            my $found = 0;
            foreach my $l (@msgs) {
                # print "Checking: $l";
                if($ti->{MSGPATTERN}) {
                    $found = ($l =~ m%$ti->{MSG}%);
                } else {
                    $found = (0 <= index($l, $ti->{MSG}));
                }
                if($found) { last; }
            }
            if(! $found) {
                warn "Cannot " . ($ti->{MSGPATTERN} ? 'match' : 'find') . 
                    " \"$ti->{MSG}\" in output of test $t";
                if(! defined($ENV{KEEPGOING})) {
                    die "";
                }
            }
        } else {
            print "Test $t (line $ti->{LINE}) was successful\n";
            unlink $msgfile;
        }
    }
}

1;


