
#
# Regression testing module
# George Necula (necula@cs.berkeley.edu)
#
package RegTest;

require 5.00;
require File::Basename;
require File::Copy;
require Getopt::Long;
require Cwd;
use Data::Dumper;
use strict;

# Authors: George Necula (necula@cs.berkeley.edu)


# Set filename parsing according to current operating system.
File::Basename::fileparse_set_fstype($^O);

if($^O eq 'MSWin32') {
    require Win32;
}

# unbuffer stdout, if it happens to be a file handle
{ my $ofh = select STDOUT;
  $| = 1;
  select $ofh;
}

# &Getopt::Long::Configure('pass_through'); # Does not work on Linux

# Set a signal handler
my $interrupt = 0; # Will set this and we'll poll it between tests
my $timeout = 0;
sub intHandler {
    my $signame = shift;
    print "I got a SIG$signame\n";
    $interrupt = 1;
}

# another one, for the hack involving --showoutput
my $gotSigUsr1 = 0;
sub usr1Handler {
    $gotSigUsr1 = 1;
}
sub setUsr1Handler {
    $gotSigUsr1 = 0;
    $SIG{'USR1'} = \&usr1Handler;
}
    

                                # Create an exception handler
sub setInterruptHandler {
    $SIG{'INT'} = \&intHandler;

    # sm: 'CLD' is the child-death signal, which we always
    # get when a child exits
#    $SIG{'CLD'} = \&intHandler;
}

&setInterruptHandler();

sub processInterrupt {
    my($self) = @_;
    if($interrupt) {
        $interrupt = 0;
        print "\n";
        my $answer = 
            &promptYN("You pressed CTRL-C. Want to continue? (y/n): ",
                      'N');
        if($answer eq "Y") {
            &setInterruptHandler();
            return;
        }

        $answer = 
            &promptYN("Will exit now. Do you want to keep the log file? (y/n):"
                      , 'Y');
        if($answer eq "N") {
            print "I am deleting $self->{LogFile}\n";
            unlink $self->{LogFile};
        }
        die "I'm outta here\n";
    }
}


use Config;
# sm: added 'if (0)' -- we don't want to install handlers
# for *all* signals!
if (0) {
    my $sg;
    foreach $sg (split(' ', $Config{sig_name})) {
        #print("Setting handler for $sg\n");
        $SIG{$sg} = \&intHandler;
    }
}
# print "signame = $Config{sig_name}\n";

# Printing for the --verbose and --gory options.
  # sm: aren't these named backwards, i.e. shouldn't vprint be for --verbose
  # and gprint be for --gory?
sub vprint {
    my $self = shift;
    if($self->{gory}) { print STDERR "@_"; }
}

sub gprint {
    my $self = shift;
    if($self->{verbose} or $self->{gory}) { print STDERR "@_"; }
}

sub mypwd {
    my $ret = `pwd`;
    chomp($ret);
    return $ret;
}

###############################
#
# The Constructor
#
###############################
# A constructor. Creates a RegTest object
#
sub new {
    my ($proto, %args) = @_;
    my $class = ref($proto) || $proto;
    # Create $self

    my $self = {};
    # Pass on everything from args into $self
    my $k;
    foreach $k (keys %args) {
        $self->{$k} = $args{$k};
    }
    bless $self, $class;

    #
    # Process the command line options
    #
    $Getopt::Long::bundling = 1;
    my @extraopt = $self->extraOptions();

    my (%option);
    &Getopt::Long::GetOptions
        (\%option,
         "--help",            # Display help information
         "--verbose|v",       # Display information about programs invoked
         "--gory",            # Display lots of information about programs
         "--debug!",          # Run the debug version of spj
         "--run|r",           # Run the tests
         "--dryrun|n",        # Pretend to run the tests
	 "--all",             # Enable all tests, even if disabled by default
         "--group=s@",        # Run a group of tests
         "--nogroup=s@",      # Omit a group of tests
         "--one=s",           # Run a single test
         "--param|p=s",       # Report on a parameter
         "--sort|s=s",        # Sort by the given parameters
         "--log=s",           # The log file
         "--logversions=i",   # How many versions of the log file to keep
         "--listtests",       # Show the tests and their group memberships
         "--stoponerror",     # Stop at the first error
         "--showoutput",      # Show the output on the console
         "--regrtest",        # enable a variety of regrtest-like behaviors
         "--timeout=i",       # timeout (seconds)
         "--skip=i",          # skip a certain number of tests on startup
         "--stopAfter=i",     # stop after the given test number
         "--extraArgs=s",     # additional argument to pass to each test command
         @extraopt
         );

    if($option{help}) {
        $self->printHelp();
        exit 0;
    }
    $self->{option}     = \%option;
    $self->{gory}       = $option{gory};
    $self->{verbose}    = $option{verbose};
    $self->{regrtest}   = $option{regrtest};
    $self->{timeout}    = (defined($option{timeout}) ? $option{timeout} 
                          : (defined($self->{DefaultTimeout}) 
                             ? $self->{DefaultTimeout} : 60));

    # Initialize the list of tests
    my %tests = ();
    $self->{tests} = \%tests;

    if(defined($option{log})) {
        $self->{LogFile} = $option{log};
    } else {
        if(! defined($self->{LogFile})) {
            $self->{LogFile} = "tests.log";
        }
    }

    if(! defined($option{logversions})) {
        $option{logversions} = 5;
    }


    # counter for tests, which gives a sometimes more convenient
    # naming scheme for tests
    $self->{testCounter} = -1;

    # sm: I want to maintain counters of what happened this run, rather
    # than doing log analysis
    $self->{numExSuccess} = 0;
    $self->{numUnexSuccess} = 0;
    $self->{numExFailure} = 0;
    $self->{numUnexFailure} = 0;

    # but, I want a log of the unexpected events.. perhaps I could get
    # this information by analyzing the existing logfiles, but what I
    # want is so simple..
    $self->{smLogfile} = mypwd() . "/testsafec.smlog";
    system("rm $self->{smLogfile} 2>/dev/null");


    return $self;
}

# print "ARGV after GetOptions = ", join(' ', @ARGV), "\n";

# Help message printing routine.
sub printHelp {
    my ($self, $scriptname) = @_;
    my ($scriptname, $extra) = $self->extraHelpMessage();
    my $availparams = $self->{AvailParams};
    my $params = "";
    my $p;
    foreach $p (keys %{$availparams}) {
        $params .= "                                   $p\n";
    }
    print << "EOF";
Usage: $self->{CommandName} [options]
Options:
  --help                       Display this information
  --verbose (or -v)            Display information about invoked sub-processes
  --gory                       Display lots of information about sub-processes
  --run|-r                     Recreate the database by running all the tests
  --dryrun|-n                  Show the commands that would be executed
  --group                      <name> Run a group of tests. This option can be 
                               specified multiple times. Only the specified
                               groups are considered, if this option is
                               present. If the option is missing run all
                               enabled tests.
  --nogroup                    <name> Do not run a group of tests. This option
                               can be specified multiple times. Exclude from
                               the executed tests the mentioned ones. This 
                               option is processed after all group options are
                               processed. 
  --listtests                  List the tests and their group memberships
  --all                        Enable all tests, even those disabled by 
                               default.  Useful in --listtests -all
  --one                        <name> Run a single test
  --param|-p=<pnames>          Create a report with values of the named 
                               parameters (separated by :). Use "ALL" for all
                               parameters. The available parameters are:
$params
  --sort=<pnames>              Sort the report by the given parameters.
  --log=<name>                 The name of a log file to operate on. 
  --logversions=<nr>           How many old versions of the log file to keep
  --stoponerror                Stop at the first error
  --showoutput                 Show the output on the console
  --timeout=ss                 Stop the command after ss seconds. Use 0 to disable.
$extra

Report bugs to necula\@cs.berkeley.edu.
EOF
}
sub extraHelpMessage {
    my($self) = @_;
    return ("RegTest", "");
}


sub initialize {
}


sub extraOptions {
    my($self) = @_;
    return ();
}

#
# Return a hash mapping parameter names either to 1 if the parameter is
# numeric or to 0 
sub availableParameters {
    my($self) = @_;
    return ('SUCCESS' => 1);
}

#
# Run a shell command
# In a given directory
# with given destinations for stdout, stderr ("" for no redirection)
sub runCommand {
    my($self, $tst, $dir, $cmd, $stdoutFile, $stderrFile) = @_;

    my $dryrun = $self->{option}->{dryrun};

    my $newcmd = $cmd;
    if($^O eq "MSWin32") {
           # Split the command arguments and the arguments
        my ($command, @args) = split(/ /, $cmd);
        my $arg = join(' ', @args);
           # use slashes
        $command =~ s|\\|/|g;
           # escape some "sh" special characters in the arguments
        $arg     =~ s|\\|\\\\|g;
        $arg     =~ s|;|\\;|g;
        $arg     =~ s|\$|\\\$|g;

        if ($stdoutFile) {
            # sm: I think this does what it used to, but of course
            # I can't easily test it..
            $arg .= " 2>$stderrFile >$stdoutFile";
        }

           # Pass everything through sh.exe
        $newcmd = "sh -c \"$command $arg\"";
    }
    else {
        # The Unix branch.

        # sm: why do we split commands and escape metacharacters?  it seems
        # to me the command itself might want to contain metacharacters
        # for their meta-effect, and could easily escape those for which
        # it wants no meta-effect ..

           # Split the command arguments and the arguments
        my ($command, @args) = split(/ /, $cmd);
        my $arg = join(' ', @args);
           # escape some "sh" special characters in the arguments
        $arg     =~ s|\\|\\\\|g;
        $arg     =~ s|;|\\;|g;
        $arg     =~ s|\$|\\\$|g;

        # The comment in PCC/bin/PCC.pm is pertinent here.
        $newcmd = "$command $arg";

        if ($stdoutFile) {
            if ($self->{option}->{showoutput}) {
                # wrap up the command in some tees and subshells so the
                # output will go to the specified files in addition to
                # the terminal (or more generally, this process' stdout/err);
                # we also have to play games with signals to detect errors..
                # (personal reminder: my test script is ~/scripts/teetwo)
                setUsr1Handler();
                $newcmd = "exec 3>&1; exec 4>&2; ".
                          "(($newcmd || kill -USR1 $$) | ".
                          "tee $stdoutFile >&3) 2>&1 | ".
                          "tee $stderrFile >&4";
            }
            else {
                $newcmd = "$newcmd 2>$stderrFile >$stdoutFile";
            }
        }
    }

    if($dryrun) {
        if (!$self->{regrtest}) {
            print " $newcmd\n";
        }
        return 0;
    } else {
        $self->gprint("\n  [Running $newcmd]");

        my $olddir = Cwd::cwd();
        if(chdir $dir) {
            my $res;
            eval { 
                local $SIG{ALRM} = sub { die "got timeout"; };
                my $timeout = $self->{timeout};
                if(defined $tst->{Timeout}) {
                    $timeout = $tst->{Timeout};
                }
                alarm $timeout;
                $res = system($newcmd);
                alarm 0; # clear the alarm
            };
            if($@ =~ m/got timeout/) {
#                print STDERR "Got timeout. Kill children\n";
                print STDERR "  TIMEOUT ";
                open(ERR, ">>$stderrFile");
                print ERR "Error: TIMEOUT ($self->{timeout}s)";
                close(ERR);
                # Kill the children
                local $SIG{HUP} = 'IGNORE';
                kill HUP => -$$;
                &setInterruptHandler();
                $res = (1 << 7) + 1
            }

            if ($gotSigUsr1) {
                $self->gprint("[exited: usr1]");
                $res = 2 << 8;     # no signal, exit code 2
            }
            else {
                $self->gprint("[exited: $res]");
            }

            # check the result code for termination by Ctrl-C,
            # which is the 'INT' signal (signal 2)
            my $signal_num = $res & 127;
            if ($signal_num == 2) {
              #print("Ctrl-C pressed\n");
              $interrupt = 1;
            }

            chdir $olddir;
            return $res;
        } else {
            print "\nCannot change to directory $dir to run $newcmd\n";
            return 1;
        }
    }
}

# All the %args are the placed into the new test
#
# The following arguments are useful:
# Name => "...",              Must be present
# Dir => "...",               default to cwd
# Cmd => "...",               no default. Use if you want to use the default
#                             "run" method. Do not redirect outputs !
# Enabled => 1/0,             defaults to 1
# Group => [ "...", "..."]    defaults to empty
# Comm => "..." a comment to be printed
# Timeout => 40,              seconds of timeout
# ErrorMsg => "..." an error message to be printed if there is an error
#
sub newTest {
    my ($self, %args) = @_;

    # make a new test
    my $new = { };

    # Move the %args into $new
    my $k;
    foreach $k (keys %args) {
        $new->{$k} = $args{$k};
    }

    if(! defined($new->{Name})) {
        die "Test does not have a name\n";
    }

    if(! defined($new->{Enabled})) {
        $new->{Enabled} = 1;
    }
    if(! defined($new->{Dir})) {
        $new->{Dir} = Cwd::cwd();
    }


    # Add itself to the regression test
    my $tests = $self->{tests};
    $tests->{$new->{Name}} = $new;

    $new->{ErrorCode} = -1;  # not yet seen

    return $new;
}

sub getTest {
    my($self, $name) = @_;
    return $self->{tests}->{$name};
}


sub cloneTest {
    my($self, $name, $newname) = @_;
    my $t = $self->getTest($name);
    if(! defined $t) {
        die "Cannot clone test $name";
    }
    my %args = %{$t}; # Make a copy
    if(defined $self->getTest($newname)) {
        die "The name $newname for the cloned test alredy used";
    }
    $args{Name} = $newname;
    $self->newTest(%args);
}


# Run the tests and collect the output in a specified logFile
sub runTests {
    my ($self, $logfile) = @_;
    my $dryrun = $self->{option}->{dryrun};

    # Place a description in the log file
    my ($hostname, $aliases, $type, $len, $thataddr) =
        gethostbyname("localhost");
    # Create the log file
    if(! $dryrun) {
        open(GLOBLOG, ">$logfile") || die "Cannot create log file $logfile";
        print GLOBLOG "Testsuite ran on " .
            localtime(time) . " on $hostname\n";
        close(GLOBLOG) || die "Cannot close $logfile";
    }
    my %tests = %{$self->{tests}};

    my @tstnames = keys %tests;
    my $tstname;
    my $nrtests = 0; # Count the enabled tests
    foreach $tstname (@tstnames) {
        my $tst = $tests{$tstname};
        if(! $tst->{Enabled}) {
            next;
        }
        $nrtests ++;
    }
    if ($self->{regrtest}) {
        print ("There are $nrtests tests enabled\n");
    }

    my $theOne = $self->{option}->{one};

    my $count = 0;
    # Sort the test names in alphabetical order
    @tstnames = sort @tstnames;
    foreach $tstname (@tstnames) {
        my $tst = $tests{$tstname};
        if(! $tst->{Enabled}) {
            next;
        }

        if (defined($theOne) &&
            $tstname ne $theOne) {
            next;
        }

        if (defined($self->{option}->{stopAfter}) &&
            ($self->{option}->{stopAfter} <= $self->{testCounter})) {
            last;
        }

        $self->processInterrupt();
        $count ++;
        if(! $dryrun) {
            open(GLOBLOG, ">>$logfile")
                || die "Cannot create log file $logfile";
        }
        my $msg = "Starting test $count/$nrtests on " . localtime(time) .
            ": $tstname";
        if (!$self->{regrtest}) {   # sm: don't want this..
          print $msg;
        }
        my $lfile = Cwd::cwd() . "/__log";
        my $lfilestdout = Cwd::cwd() . "/__log.stdout";
        # Try to delete the file. If we cannot then somebody is hanging to
        # them and we will not see any output
        if((-f $lfile && ! unlink $lfile) || 
           (-f $lfilestdout && ! unlink $lfilestdout)) {
            die "\nCannot delete $lfile or $lfilestdout. Some process is hanging on to them";
        }

        if(! $dryrun) {
            print GLOBLOG "\n===================================\n$msg\n";
            close(GLOBLOG) || die "Cannot close $logfile";
        } elsif (!$self->{regrtest}) {
            print "\n";
        }
       
        my $extracmd = "";
        #if(defined ($self->{option}->{showoutput})) {
        #    $extracmd = " | tee $lfilestdout 2>$lfile ";
        #} else {
        #    $extracmd = " 2>$lfile >$lfilestdout ";
        #}
        my $res = $self->run($tst, $extracmd, $dryrun,
                             $lfilestdout, $lfile);
        if(! $dryrun) {
            # Now copy over logs
            open(GLOBLOG, ">>$logfile")
                || die "Cannot create log file $logfile";
            if(open(ERRLOG, "<$lfile")) {
                while(<ERRLOG>) {
                    print GLOBLOG $_;
                }
                close(ERRLOG) || die "Cannot close $lfile";
                unlink $lfile;
            }
            if(open(STDLOG, "<$lfilestdout")) {
                print GLOBLOG "\n    === STDOUT ===\n";
                while(<STDLOG>) { print GLOBLOG $_; }
                close(STDLOG) || die "Cannot close $lfilestdout";
                unlink $lfilestdout;
            }
            close(GLOBLOG) || die "Cannot close $logfile";
            unlink "$logfile.stdout";

            # analyze success/failure
            if($self->expectedToFail($tstname) ? !$res : $res) {
                # test resolved the opposite way from what was expected
                if (! $self->{regrtest}) {
                    print "\t--FAILED\n";
                }
                if(defined $self->{option}->{stoponerror}) {
                    #die "You told me to stop on error";
                    exit 2;     # sm: don't need the explanation
                }
            }

            else {
                # test resolved the way it was expected to
                if (!$self->{regrtest}) {
                    print "\n";
                }
            }
        }
    }
}


# return true if the test is expected to fail
sub expectedToFail {
  my ($self, $tname) = @_;
  my $tst = $self->{tests}->{$tname};
  if (defined($tst) &&     # what the hey..
      (defined($tst->{MustFail}) || defined($tst->{Comm}))) {
    return 1;
  }
  else {
    return 0;
  }
}


# Open an existing logfile and parse it.
sub parseLogFile {
    my($self, $logfile) = @_;

    print "Parsing logfile $logfile\n";
    my $currentTestName = "";
    my $currentTest;
    my $tests = $self->{tests};
    open(LOG, "<$logfile") || die "Cannot open the log file $logfile (cwd=" . Cwd::cwd() .")";
    my $date = <LOG>;
    $date =~ s/^Testsuite ran at (.+) on (.+)$/$1/;
    while(<LOG>) {
        if($_ =~ m|^Starting test \d+/\d+ on .+:\d\d:\d\d \d\d\d\d: (\S+)|) {
            # print "Found start of $1 (defined = ", defined($currentTest), ")\n";
            # Finish the previous test case
            if(defined $currentTest) {
                $self->finishParsingLog($currentTest);
            }
            # Find the test with this name
            $currentTest = $self->getTest($1);
            if(defined $currentTest) {
                # print "Start parsing log for $currentTest->{Name}\n";
                # Start the parsing
                $self->startParsingLog($currentTest);
            }
        }
        if(defined($currentTest)) {
            # Recognize the TIMEOUT error
            if($_ =~ m|^Error: TIMEOUT|) {
                $currentTest->{ErrorCode} = 100;
                $currentTest->{ErrorMsg} = $_;
            }
            # Do the specialized parsing
            $self->parseLogLine($currentTest, $_);
        }
    }
    # Finish parsing the last test
    if(defined($currentTest)) {
        $self->finishParsingLog($currentTest);
    }
    close(LOG);
    return ($date);
}


# 
# Show a list of test cases
# Arguments: 
#   - heading of the set of test cases
#   - a list of test cases
sub showList {
    my($self, @lst) = @_;
    my $tst;
    # Sort the list by name
    @lst = sort {$a->{Name} cmp $b->{Name}} @lst;
    foreach $tst (@lst) {
        my $comm = defined($tst->{Comm}) ? "\n\t-$tst->{Comm}" : "";
        my $errmsg = 
            defined($tst->{ErrorMsg}) ? "\n\t$tst->{ErrorMsg}" : "";
        print "  $tst->{Name}$comm$errmsg\n";
    }
}

sub showListHeader {
    my($self, $title, $code, $totalenabled, @lst) = @_;
    my $tests = $self->{tests};
    my $count = $#lst + 1;
    my $ratio = $totalenabled == 0 ? 0 : 100 * $count / $totalenabled;
    printf "%s(%d)   %02d%% (%d / %d) [%d tests disabled]\n", $title,
           $code,
           $ratio, $count, $totalenabled, 
           (scalar keys %$tests) - $totalenabled;
}

sub processGroup {
    my($self, $group, $toAdd) = @_;
    my $tstname;
    my $count = 0;
    my %tests = %{$self->{tests}};
  ITER: 
    foreach $tstname (keys %tests) {
        if((defined $tests{$tstname}->{Group})) {
            my $i;
            my @arr = @{$tests{$tstname}->{Group}};
            my $size = $#arr;
            for($i=0; $i <= $size; $i++) {
                if($arr[$i] eq $group) {
                    if(($toAdd ? 1 : 0) != 
                       ($tests{$tstname}{Enabled} ? 1 : 0)) {
                        $count++;
                    }
                    $tests{$tstname}{Enabled} = $toAdd;
                    next ITER;
                }
            }
        }
    }
    if($count == 0) {
        warn "Cannot find any tests in group $group\n";
    }
    my $str = ($toAdd ? "Enabled" : "Disabled");
    print STDOUT "$str $count tests in group $group\n";
}


# A subroutine that deletes or renames a version of the log file 
# The first version is called <base>.1, ... where <base> is the current log
# file
sub deleteOrRenameLog {
    my($self, $logbase, $version) = @_;
    my $verlogname = $version == 0 ? $logbase : "$logbase.$version";
    if(! -f $verlogname) {
        return;
    }
    if($version >= $self->{option}->{logversions}) {
        # delete it 
        unlink $verlogname;
        return;
    }
    # See if we can rename it to a higher version
    my $newversion = $version + 1;
    $self->deleteOrRenameLog($logbase, $newversion);
    rename $verlogname, "$logbase.$newversion";
}

# The main entry point
sub doit {

    my ($self) = @_;
    my %option = %{$self->{option}};
    my %tests = %{$self->{tests}};
    # Get the logfile name
    my $logFile = $self->{LogFile};
    
    # Go through the directory in which $logFile is and find all files with 
    # similar names
    my @existingLogFiles = ();

    my $logDir = ".";
    my $logBase;
    {
        my ($base, $dir, $ext) = 
          File::Basename::fileparse($logFile, "");
        if(defined($dir)) {
            $logDir = $dir; $logBase = "$base$ext";
        }
        my $file;
        opendir(LOGDIR, $logDir) || die "can't open directore $logDir";
        foreach $file (readdir LOGDIR) {
            if($file =~ m|$logBase(\.\d+)?$|) {
                push @existingLogFiles, $file
            }
        }
        closedir(LOGDIR);
    }
    @existingLogFiles = sort { $a cmp $b } @existingLogFiles;

    my $results;
    

    # Enable all tests if specified
    if(defined $option{all}) {
        # Enable all tests
        my $tst;
        foreach $tst (keys %tests) {
            $tests{$tst}->{Enabled} = 1;
        }
    }
    # Prune to a group if specified
    if(defined $option{group}) {
        # First go and disable all tests
        my $tst;
        foreach $tst (keys %tests) {
            $tests{$tst}->{Enabled} = 0;
        }
        # Enable the ALWAYS group
        $self->processGroup("ALWAYS", 1);
        # No go and enable all given groups
        my $grp;
        foreach $grp (@{$option{group}}) {
            print "Enabling group $grp\n";
            $self->processGroup($grp, 1);
        }
    }
    # Prune a group if specified
    if(defined $option{nogroup}) {
        # No go and disable all given groups
        my $grp;
        foreach $grp (@{$option{nogroup}}) {
            $self->processGroup($grp, 0);
        }
    }
    
    # Show the groups if it was requested
    if($option{listtests}) {
        my $tstname;
        print "The enabled test cases are:\n";
        my @tstnames = keys %tests;
        my @sorted = sort @tstnames;
        foreach $tstname (@sorted) {
            my $tst = $tests{$tstname};
            if(! $tst->{Enabled}) { next; }
            printf "  %-40s (%s)\n", 
                    $tstname, 
                    defined $tst->{Group} ? join(',', @{$tst->{Group}}) : "";
        }
        exit 0;
    }

    # Or maybe we need to run a group
    my $hascreatedlog = 0;
    if(defined $option{run} || defined $option{dryrun}) {
        # Now rename some old log files to make room for the new one
        if(! $option{dryrun}) {
            $self->deleteOrRenameLog($logFile, 0);
            $hascreatedlog = 1;
        } else {
            print "DRY RUN: ";
        }
        if (!$self->{regrtest}) {
          print "Writing test results in logfile $logFile\n";
        }
        # Now run the tests
        $self->runTests($logFile);
    } 

    if ($self->{regrtest}) {
        # sm: finish up the way I like
        print("\n");
        print("Successful tests:     $self->{numExSuccess}\n");
        print("Failed as expected:   $self->{numExFailure}\n");
        if (!defined($self->{option}->{stoponerror})) {
            print("Unexpected success:   $self->{numUnexSuccess}\n");
            print("Unexpected failure:   $self->{numUnexFailure}\n");

            # report the unexpected events
            if ( -f $self->{smLogfile} ) {  
              print("\n");
              system("cat $self->{smLogfile}");
              system("rm $self->{smLogfile}");
            }
        }

        exit 0;
    }

    # Now select which log file to look at
    if(! $hascreatedlog) {
        if(defined $option{log}) {
            $logFile = $option{log};
        } else {
            if($#existingLogFiles >= 0) {
                my $file;
                my $id = 1;
                if($#existingLogFiles > 0) {
                    print "The following test logs are available:\n";
                    foreach $file (@existingLogFiles) {
                        my $comment;
                        my @thestat = stat("$logDir/$file");
                        my $nrbytes = $thestat[7];
                        open(LOG, "<$logDir/$file");
                        if(<LOG> =~ m|^Testsuite ran on (.+) on (.+)$|) {
                            $comment .= "$nrbytes bytes. Ran on $1 on $2";
                        }
                        close(LOG);
                        print "   $id: $file ($comment)\n";
                        $id ++;
                    }
                    $id --;
                  SelectAnother:
                    print "Select a log (1-$id, q to quit): ";
                    my $cmd = <STDIN>; chop $cmd;
                    if($cmd eq "q") {
                        exit(0);
                    }
                    if($cmd < 1 || $cmd > $id) {
                        goto SelectAnother;
                    }
                    $id = $cmd;
                }
                $logFile = @existingLogFiles[$id - 1];
            }
        }
    }
    if(! -f $logFile) {
	print "\n*** No log file exists. Use the --run command first to create  one\n\n\n";
        $self->printHelp ();
	exit 1;
    }
    # Parse the log file and set ErrorCode
    my ($results, $date) = $self->parseLogFile($logFile);

    # Collect all the ErrorCode's
    my %errcodelst = ();
    
    my $tst;
    my $nrenabled = 0;
    foreach $tst (values %tests) {
        if(! $tst->{Enabled}) { next; }
        $nrenabled ++;
        my $errcode = $tst->{ErrorCode};
        # Add it to the list for the error code
        my $errlst = $errcodelst{$errcode};
        if(! defined($errlst)) {
            $errlst = [];
            $errcodelst{$errcode} = $errlst;
        }
        push @{$errlst}, $tst;
    }

    # Now show a report sorted by error code (viewed as a number)
    my @errorcodes = sort { $a <=> $b } (keys %errcodelst);

    print "Reporting results in $logFile\n";
    # Now show those test cases that succeeded but have bad comments
    # associated with them
    my @succs = grep { defined ($_->{Comm}) } @{$errcodelst{0}}; 
    $self->showListHeader("Successes thought to fail", 0, $nrenabled, @succs);
    $self->showList(@succs);
    foreach my $errcode (@errorcodes) {
        $self->showListHeader($self->errorHeading(int($errcode)), 
                              int($errcode),
                              $nrenabled,
                              @{$errcodelst{$errcode}});
        if($errcode > 0) {
            $self->showList(@{$errcodelst{$errcode}});
        }
    }
    if(defined $option{param}) {
        $self->printReport();
    }
} 




sub sortReport {
    my ($self) = @_;
    my $sp;
    my @sortpars = @{$self->{sortpars}};

    foreach $sp (@sortpars) {
        my $res;
        if($self->{AvailParams}->{$sp}) { # Is numeric
            $res = int($a->{$sp}) <=> int($b->{$sp});
        } else {
            $res = $a->{$sp} cmp $b->{$sp};
        }
        if($res != 0) { 
            return $res;
        }
    }
    return 0;
}



sub printReport {
    my ($self) = @_;
    my %option = %{$self->{option}};
    my @sortpars;

    print "Printing report\n";
    if(defined($option{param})) {
        my @params = split(/:/, $option{param});
        if(grep(/^ALL$/, @params)) {
            @params = keys %{$self->{AvailParams}};
        }
        unshift @params, "Name";       # Name is always the first parameter

        # Now sort the report
        @sortpars = ();
        if(defined($option{sort})) {
            @sortpars = split(/:/, $option{sort});
        }
        push @sortpars, "Name";  # Add the name as the last sorting parameter
        $self->{sortpars} = \@sortpars;

        # Create a list with all successes and with the requested parameters
        my @report = ();
        my $tstname;
        foreach $tstname (keys %{$self->{tests}}) {
            my $tst = $self->{tests}->{$tstname};
            if(! $tst->{Enabled}) { next; }
            push @report, $tst;
        }
        # print "Sorting on ", join('+', @sortpars), "\n";
        my @sortedreport = sort sortReport @report;
        
        # Now print the report
        my $par;
        print "\n";
        foreach $par (@params) {
            if($par eq "Name") {
                printf "%-20s  ", $par;
            } else {
                printf "%-8s  ", $par;
            }
        }
        print "\n------------------------------------------------------\n";
        my $tst;
        foreach $tst (@sortedreport) {
            # print Dumper(\$tst);
            foreach $par (@params) {
                my $pval = $tst->{$par};
                if(! defined($pval)) { $pval = '-'; }
                if($par eq "Name") {
                    printf "%-20s   ", $pval;
                } else {
                    printf "%-8s   ", $pval;
                }
            }
            print "\n";
        }
    }
}

#
# A function to translate the error code into a report heading
sub errorHeading {
    my($self, $errcode) = @_;
    if($errcode == 0) {
        return "Success";
    }
    if($errcode == 10000) {
        return "Test should have failed";
    }
    if($errcode == 10001) {
        return "Could not find pattern in output";
    }
    return "Error $errcode";
}


# send something to stdout and to my little log file
sub smLog {
    my ($self, $msg) = @_;
    print($msg . "\n");
    system("echo \"$msg\" >> $self->{smLogfile}");
}


#
# Run a test. Return 0 if success
sub run {
    my($self, $tst, $extraArgs, $dryrun, $stdoutFile, $stderrFile) = @_;

    # sm: this test always fails because the caller tests it too ..
    if(! $tst->{Enabled}) { return 0 ; }

    my $expectFail = $self->expectedToFail($tst->{Name})? "(fail) " : "";

    # the summary line is supposed to be a command that can be copy+pasted
    # into an xterm to reproduce the failure
    my $summary = $tst->{Cmd} . $extraArgs;
    $summary =~ s/ *_GNUCC=1//;       # strip options I don't care about
    $summary =~ s/ *STATS=1//;
    $summary =~ s/ *PRINTSTAGES=1//;
    $summary =~ s/ +/ /g;             # collapse consecutive spaces
    $summary =~ s/ *$//;              # strip trailing spaces
    $self->{testCounter}++;

    my $skip = defined($self->{option}->{skip}) &&
               ($self->{option}->{skip} > $self->{testCounter})? "(skip) " : "";

    if ($self->{regrtest}) {
        # sm: regrtest-like output
        if ($skip) {
            print("skipping: [$self->{testCounter}] $expectFail$summary\n");
        }
        else {
            print("------------ [$self->{testCounter}] " .
                  "$expectFail$summary ------------\n");
        }
    }

    if ($skip) {
        return $expectFail? 1 : 0;
    }

    # add additional arguments passed at command line to entire tester
    if (defined($self->{option}->{extraArgs})) {
      $extraArgs .= $self->{option}->{extraArgs};
    }


    if (defined($tst->{ExtraArgs})) {
      $extraArgs .= " " . $tst->{ExtraArgs};
    }
 
   my $res =
        $self->runCommand($tst, 
                          $tst->{Dir},
                          $tst->{Cmd} . $extraArgs,
                          $stdoutFile, $stderrFile);

    # sm: I want ctl-c to bail immediately, no questions asked.
    # I originally put this in processInterrupt, but that doesn't
    # get called very soon after runCommand, and other stuff
    # happens in between that I didn't want.
    if ($interrupt && $self->{regrtest}) {
        print("interupted\n");
        exit 2;
    }

    # analyze success/failure (some additional analysis is done
    # in the caller, runTests)
    if ($res == 0) {   # test succeeded
        if (!$expectFail) {
            $self->{numExSuccess}++;

            if ($self->{regrtest} &&
                defined($tst->{AfterSuccessScript})) {
                if (system($tst->{AfterSuccessScript}) != 0) {
                    exit 2;    # bail if after-script fails
                }
            }
        }
        else {
            $self->{numUnexSuccess}++;

            if ($self->{regrtest}) {
                my $reason = $tst->{Comm};
                print("\n");
                $self->smLog("[$self->{testCounter}] GOOD NEWS: " .
                             "A test that used to fail ($reason) now succeeds:");
                $self->smLog("  $summary");
            }
        }
    }

    else {             # test failed
        if ($expectFail) {
            $self->{numExFailure}++;
        }
        else {
            $self->{numUnexFailure}++;

            if ($self->{regrtest}) {
                print("\n");
                $self->smLog("[$self->{testCounter}] " .
                             "A regression test command failed:");
                $self->smLog("  $summary");

                if (defined($tst->{FailDiagnosis})) {
                    print ("\n" . $tst->{FailDiagnosis} . "\n");
                }
            }
        }
    }

    return $res;
}

# Called when the parsing of the log for this test begins
sub startParsingLog {
    my($self, $tst) = @_;
    $tst->{ErrorCode} = 0;
    return;
}

# Called when the parsing of the log for this test ends
sub finishParsingLog {
    my($self, $tst) = @_;
    if(defined $tst->{MustFail}) {
        if($tst->{ErrorCode} == 0) {
            $tst->{ErrorCode} = 10000;
        } else {
            $tst->{ErrorCode} = 0; # No failure then
        }
    }
    if($tst->{ErrorCode} == 0 && # Looks like success so far
       defined $tst->{ExpectPattern} &&
       ! $tst->{FoundExpectedPattern}) {
        
        $tst->{ErrorCode} = 10001;
    }
    if($tst->{ErrorCode} == 0) {
        $tst->{SUCCESS} = 1;
    }
    # print "finishParsingLog for $tst->{Name}\n";
#    if ($tst->{Name} eq "testrun/demo1-inferbox") {
#        print Dumper($tst);
#    }
    return;
}

my $debugpat = 0;
# Called on each line of the log for this test
# Should set fields in the object
# The ErrorCode field, if set to <> 0 will signal an error
sub parseLogLine {
    my($self, $tst, $line) = @_;
    if(defined $tst->{Patterns}) {
        my $pat;
        my %patterns = %{$tst->{Patterns}};
        foreach $pat (keys %patterns) {
            my @results;
            if($line =~ m/$pat/) {
                if($debugpat) {
                    print "Matched $pat for $tst->{Name}\: $1, $2, $3, $4, $5,
$6, $7, $8, $9\n";
                }
                my $handler = $patterns{$pat};
                &{$handler}($self, $tst, $1, $2, $3, $4, $5, $6, $7, $8, $9);
            }
        }
    }
    # See if any pattern is expected
    if(defined $tst->{ExpectPattern}) {
        my $pat = $tst->{ExpectPattern};
        if ($line =~ m|$pat|) {
            $tst->{FoundExpectedPattern} = 1;
        }
    }
    return;
}


sub testExists {
    my ($self, $tname) = @_;
    return defined($self->{tests}->{$tname});
}

sub setField {
    my($self, $tname, $field, $value) = @_;
    my $tst = $self->{tests}->{$tname};
    if(! defined($tst)) {
        die "Cannot set field of nonexistent test $tname\n";
    }
    $tst->{$field} = $value;
}
sub getField {
    my($self, $tname, $field) = @_;
    my $tst = $self->{tests}->{$tname};
    if(! defined($tst)) {
        die "Cannot set field of nonexistent test $tname\n";
    }
    return $tst->{$field};
}

sub addComment {
    my($self, $tname, $comm) = @_;
    my $tst = $self->{tests}->{$tname};
    if(! defined($tst)) {
        die "Cannot add comment to nonexistent test $tname\n";
    }
    $tst->{Comm} .= $comm;
}

sub addGroups {
    my($self, $tname, @groups) = @_;
    my $tst = $self->{tests}->{$tname};
    if(! defined($tst)) {
        die "Cannot add groups to nonexistent test $tname\n";
    }
    push @groups, @{$tst->{Group}};
    $tst->{Group} = \@groups;
}

sub enable {
    my($self, $tname, $value) = @_;
    my $tst = $self->{tests}->{$tname};
    if(! defined($tst)) {
        die "Cannot enable to nonexistent test $tname\n";
    }
    $tst->{Enabled} = $value;
}

sub prompt {
    my($msg) = @_;
    print $msg;
    my $answer = <STDIN>;
    if($answer =~ m|^([^\r\n]*)[\r\n]+|) {
        $answer = $1;
    }
    return $answer;
}

sub promptYN {
    my($msg, $default) = @_;
    my $counter = 5;
    while(1) {
        my $answer = &prompt($msg);
        if($answer eq "") { 
            # Perhaps we have no input
            if(eof(STDIN)) { 
                return $default; 
            }
            next; 
        }
        if($answer eq 'y' || $answer eq 'Y') { return 'Y'; }
        if($answer eq 'n' || $answer eq 'N') { return 'N'; }
    }
}
    

1;



