use strict;
use DBI;
my $RULE_LENGTH = 20;
my $numArgs = $#ARGV + 1;
my $printFileInfo = 0;
my $shouldPrint = 0;
my $filename = $ARGV[0];
# terrible hack :(
my $dbh = DBI->connect("dbi:SQLite:dbname=maudeProfileDBfile.sqlite","","");
# {PrintError => 0}
if ($numArgs == 2) {
	my $flag = $ARGV[1];
	if ($flag eq "-c") {
		$printFileInfo = 1;
	}
	if ($flag eq "-p") {
		$shouldPrint = 1;
	}
}
if ($numArgs == 3) {
	my $flag = $ARGV[1];
	if ($flag eq "-c") {
		$printFileInfo = 1;
	}
	if ($flag eq "-p") {
		$shouldPrint = 1;
	}
	$flag = $ARGV[2];
	if ($flag eq "-c") {
		$printFileInfo = 1;
	}
	if ($flag eq "-p") {
		$shouldPrint = 1;
	}
}
if ($shouldPrint) { printData(); exit 0; }
if ($printFileInfo) {printFileInfo(); exit 0; }
# if ($shouldClean) { $dbh->do("DROP TABLE IF EXISTS data;");}
$dbh->do("CREATE TABLE data (file NOT NULL, rule NOT NULL, type NOT NULL, kind NOT NULL, rewrites BIGINT NOT NULL, matches BIGINT, fragment NULL DEFAULT NULL, initialTries NULL DEFAULT NULL, resolveTries NULL DEFAULT NULL, successes NULL DEFAULT NULL, failures NULL DEFAULT NULL, PRIMARY KEY (file, rule))");
$dbh->do("PRAGMA default_synchronous = OFF");

my $sql = "INSERT INTO data (file, rule, type, kind, rewrites, matches) VALUES ('$filename', ?, ?, ?, ?, ?)";
my $insertOpHandle = $dbh->prepare($sql);
# $sql = "INSERT INTO data (rule, type, kind, rewrites, matches) VALUES (?, ?, ?, ?, ?)";
my $insertEqHandle = $insertOpHandle;
$sql = "INSERT INTO data (file, rule, type, kind, rewrites, matches, fragment, initialTries, resolveTries, successes, failures) VALUES ('$filename', ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)";
my $insertCeqHandle = $dbh->prepare($sql);
# $sql = "UPDATE data SET count = count + 1, rewrites = rewrites + ?, matches = matches + ? where rule = ? AND type = ? AND kind = ?";
# my $updateOpHandle = $dbh->prepare($sql);
# # $sql = "UPDATE data SET rewrites = rewrites + ?, matches = matches + ? where rule = ? AND type = ? and kind = ?";
# my $updateEqHandle = $updateOpHandle;
# $sql = "UPDATE data SET count = count + 1, rewrites = rewrites + ?, matches = matches + ?, fragment = fragment + ?, initialTries = initialTries + ?, resolveTries = resolveTries + ?, successes = successes + ?, failures = failures + ? where rule = ? AND type = ?";
# my $updateCeqHandle = $dbh->prepare($sql);
				
open(MYINPUTFILE, "<$filename");
my $line = <MYINPUTFILE>;
# skip header if it's there
if (index($line,"\||||||||||||||||||/") != -1){
	$line = <MYINPUTFILE>; $line = <MYINPUTFILE>;
	$line = <MYINPUTFILE>; $line = <MYINPUTFILE>;
	$line = <MYINPUTFILE>; $line = <MYINPUTFILE>;
}

# after first ==========================================
while(<MYINPUTFILE>) {
	my $line = $_;
	chomp($line);
	if ($line =~ m/^op /){
		handleOp($line, *MYINPUTFILE);
	} elsif ($line =~ m/^eq /){
		handleEq($line, *MYINPUTFILE, 'eq');
	} elsif ($line =~ m/^ceq /){
		handleCeq($line, *MYINPUTFILE, 'ceq');
	} elsif ($line =~ m/^rl /){
		handleEq($line, *MYINPUTFILE, 'rl');
	} elsif ($line =~ m/^crl /){
		handleCeq($line, *MYINPUTFILE, 'crl');
	} else {
		#print "--------------------\n$line\n--------------------\n";
	}
}

$dbh->disconnect;


#############################################
sub handleOp {
	my ($line, $file) = @_;
	my $rule = substr($line, 3);
	$line = <$file>;
	if ($line =~ m/built-in eq rewrites: (\d+) \(/){
		my $rewrites = $1;
		my $retval = $insertOpHandle->execute($rule, 'op', 'builtin', $rewrites, $rewrites);
		# if (!$retval) {
			# $updateOpHandle->execute($rewrites, $rewrites, $rule, 'op', 'builtin');
		# }
		return;
	}
}
sub handleEq {
	my ($line, $file, $type) = @_;
	my $rule = $line;
	my $kind = 'macro';
	while (<$file>){
		$line = $_;
		chomp($line);
		if ($line =~ m/^rewrites: (\d+) \(/){
			my $rewrites = $1;
			my $retval = $insertEqHandle->execute($rule, $type, $kind, $rewrites, $rewrites);
			# if (!$retval) {
				# $updateEqHandle->execute($rewrites, $rewrites, $rule, $type, $kind);
			# }
			return;
		} if ($line =~ m/[\[ ]label ([^ ]+)[\] ]/){ # labeled equation
			$rule = $1;
			# print "$1\n"
		} if ($line =~ m/structural rule/) {
			$kind = 'structural';
		} if ($line =~ m/computational rule/) {
			$kind = 'computational';
		} else {
			$rule .= "$line\n";
		}
	}
}
sub handleCeq {
	my ($line, $file, $type) = @_;
	my $rule = $line;
	my $kind = "macro";
	while (<$file>){
		$line = $_;
		chomp($line);
		if ($line =~ m/^lhs matches: (\d+)	rewrites: (\d+) \(/){
			my $matches = $1;
			my $rewrites = $2;
			$line = <$file>;
			$line = <$file>;
			chomp($line);
			$line =~ m/^(\d+)\t\t(\d+)\t\t(\d+)\t\t(\d+)\t\t(\d+)/;
			my $fragment = $1;
			my $initialTries = $2;
			my $resolveTries = $3;
			my $successes = $4;
			my $failures = $5;
			
			my $retval = $insertCeqHandle->execute($rule, $type, $kind, $rewrites, $matches, $fragment, $initialTries, $resolveTries, $successes, $failures);
			# if (!$retval) {
				# $updateCeqHandle->execute($rewrites, $matches, $fragment, $initialTries, $resolveTries, $successes, $failures, $rule, $type, $kind);
			# }
			return;
		} if ($line =~ m/[\[ ]label ([^ ]+)[\] ]/){ # labeled equation
			$rule = $1;
			# print "$1\n"
		} if ($line =~ m/structural rule/) {
			$kind = 'structural';
		} if ($line =~ m/computational rule/) {
			$kind = 'computational';
		} else {
			$rule .= "$line\n";
		}
	}
}


sub printData {
# SELECT a.file, a.rule, a.type, a.kind, SUM(a.rewrites), 
		# SUM(a.matches), SUM(a.fragment), SUM(a.initialTries), 
		# SUM(a.resolveTries), SUM(a.successes), SUM(a.failures)
	my $sth = $dbh->prepare("
	SELECT count(a.file) as count, a.rule, a.kind, 
	sum(a.rewrites) as rewrites, SUM(a.matches) as matches
	FROM data a
	WHERE a.type != 'op' AND a.kind != 'macro'
	GROUP BY a.rule
	--- , a.type, a.kind
	--- ORDER BY a.matches DESC
	") or die $dbh->errstr;
	$sth->execute();
	# Fragment, Initial Tries, Resolve Tries, 
	print "Rule, Count, Kind, Matches, Rewrites\n";
	while (my $hash_ref = $sth->fetchrow_hashref) {
		my $rule = substr($hash_ref->{rule}, 0, $RULE_LENGTH);
		$rule =~ tr{\n}{ }; # turn newlines into spaces
		$rule =~ s/["]/""/g; # escape quotes
		# my $file = $hash_ref->{file};
		# my $type = $hash_ref->{type};
		my $count = $hash_ref->{count};
		my $kind = $hash_ref->{kind};
		my $rewrites = $hash_ref->{rewrites};
		my $matches = $hash_ref->{matches};
		# my $fragment = $hash_ref->{fragment};
		# my $initialTries = $hash_ref->{initialTries};
		# my $resolveTries = $hash_ref->{resolveTries};
		# my $successes = $hash_ref->{successes};
		# my $failures = $hash_ref->{failures};
		print "\"$rule\", $count, $kind, $matches, $rewrites\n";
		# $fragment, $initialTries, $resolveTries, 
	}
	$dbh->disconnect();
}

sub printFileInfo {
	my $sth = $dbh->prepare("
	SELECT a.file, count(a.rule) as count,
	sum(a.rewrites) as rewrites, SUM(a.matches) as matches
	FROM data a
	WHERE a.type != 'op' AND a.kind != 'macro'
	GROUP BY a.file
	ORDER BY a.file
	--- , a.type, a.kind
	--- ORDER BY a.matches DESC
	") or die $dbh->errstr;
	$sth->execute();
	# Fragment, Initial Tries, Resolve Tries, 
	print "File, Count, Rewrites, Matches\n";
	while (my $hash_ref = $sth->fetchrow_hashref) {
		my $rule = substr($hash_ref->{rule}, 0, $RULE_LENGTH);
		$rule =~ tr{\n}{ }; # turn newlines into spaces
		$rule =~ s/["]/""/g; # escape quotes
		my $file = $hash_ref->{file};
		# my $type = $hash_ref->{type};
		my $count = $hash_ref->{count};
		# my $kind = $hash_ref->{kind};
		my $rewrites = $hash_ref->{rewrites};
		my $matches = $hash_ref->{matches};
		print "$file, $count, $rewrites, $matches\n";
		# $fragment, $initialTries, $resolveTries, 
	}
	$dbh->disconnect();
}
