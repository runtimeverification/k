#!/usr/bin/perl
$^W = 1; # turn on warnings
#use sigtrap 'handler' => \&INT_handler, 'INT';
#$SIG{'INT'} = 'INT_handler'; # handle control-c
$| = 1; # autoflush to console

use strict;
use IO::Socket; 
use IPC::Open2;
use POSIX ":sys_wait_h";

my $PID = 0;
my $MAUDE_EOF = '###EOMTCP###';
my $READFILE = '###READFILE###';
my $WRITEFILE = '###WRITEFILE###';

my $NOT_EXISTS = -3;
my $NOT_READABLE = -4;
my $NOT_WRITEABLE = -5;
my $EXISTS = -6;
my $UNKNOWN = -7;


######################################################
# Main
######################################################

my $sock = new IO::Socket::INET (
	LocalHost => 'localhost', 
	LocalPort => '7077', 
	Proto => 'tcp',
	Listen => 25, 
	ReuseAddr => 1, 
	#ReusePort => 1
); 
die "Could not create socket: $!\n" unless $sock;
$sock->autoflush();
while(1) { 
	print "-----------------------------------------------------------\n";
	my $new_sock = $sock->accept();
	handleConnection($new_sock);
}
$sock->shutdown(2);
close($sock);


######################################################
# subroutines
######################################################

sub handleConnection {
	my ($sock) = (@_);
	my $request = "";
	do {
		$request .= <$sock>;
	} while (index($request, $MAUDE_EOF) == -1); # until we are sure maude is done sending
	
	$request = substr($request, 0, index($request, $MAUDE_EOF)) ;
	if ($request =~ m/^$READFILE(.*)/){
		my $filename = $1;
		print "request to read: $filename\n";
		print $sock handle_read($1);
	} elsif ($request =~ m/^$WRITEFILE(.*[^\\])\|(.*)/) {
		my $filename = $1;
		my $data = $2;
		print "request to write: $filename\n";
		print $sock handle_write($1, $2);
	} else {
		print "Didn't know how to handle request: $request\n";
		print $sock errmsg($UNKNOWN);
	}
	$sock->shutdown(2);
	close($sock);
}

sub handle_read {
	my ($filename) = @_;
	if (! -e $filename) {
		return errormsg($NOT_EXISTS);
	}
	open FILE, $filename or return errormsg("Couldn't open file: $!");
	my @lines = <FILE>;
	return succmsg(join('',@lines));
}

sub handle_write {
	my ($filename, $data) = @_;
	if (-e $filename) {
		return errormsg($EXISTS);
	}
	open FILE, '>', $filename or return errormsg("Couldn't open file: $!");
	print FILE $data;
	close FILE or return errormsg("Couldn't close file: $!");
	return succmsg(0);
}

sub errormsg {
	my ($msg) = @_;
	return "###ERR###$msg";
}

sub succmsg {
	my ($msg) = @_;
	return "###SUCC###$msg";
}

# sub tryCVC3 {
	# my ($query) = @_;
	# my($chld_out, $chld_in);
	# print "trying cvc3\n";
	# $PID = open2($chld_out, $chld_in, 'cvc3', '-lang', 'smtlib', '-timeout', '1');
	# print $chld_in "$query";
	# close($chld_in);
	# $SIG{ALRM} = sub { print "CVC3 timed out\n"; kill 9 => $PID; };
	# ualarm($TIMEOUT);
	# my $result = <$chld_out>;
	# alarm 0;
	# waitpid $PID, 0;
	# if (defined($result)){
		# print "cvc3 got $result\n";
	# } else {
		# print "cvc3 failed\n";
		# $result = 'sat';
	# }
	# return ($result);
# }


# sub INT_handler {
	# print "\n caught $SIG{INT}",@_,"\n";
	# close($sock);
	# kill 6, $$;
# }
