use strict;
use DBI;
my $RULE_LENGTH = 200;
my $numArgs = $#ARGV + 1;
my $shouldClean = 0;
my $shouldPrint = 0;
# terrible hack :(
if ($numArgs == 1) {
	my $flag = $ARGV[0];
	if ($flag eq "-c") {
		$shouldClean = 1;
	}
	if ($flag eq "-p") {
		$shouldPrint = 1;
	}
}
if ($numArgs == 2) {
	my $flag = $ARGV[0];
	if ($flag eq "-c") {
		$shouldClean = 1;
	}
	if ($flag eq "-p") {
		$shouldPrint = 1;
	}
	$flag = $ARGV[1];
	if ($flag eq "-c") {
		$shouldClean = 1;
	}
	if ($flag eq "-p") {
		$shouldPrint = 1;
	}
}

my $dbh = DBI->connect("dbi:SQLite:dbname=maudeProfileDBfile.sqlite","","", {PrintError => 0});
if ($shouldClean) { $dbh->do("DROP TABLE IF EXISTS data;");}
$dbh->do("CREATE TABLE data (rule NOT NULL, type NOT NULL, rewrites BIGINT NOT NULL, matches BIGINT, fragment NULL DEFAULT NULL, initialTries NULL DEFAULT NULL, resolveTries NULL DEFAULT NULL, successes NULL DEFAULT NULL, failures NULL DEFAULT NULL, PRIMARY KEY (type, rule))");
$dbh->do("PRAGMA default_synchronous = OFF");

open(MYINPUTFILE, "<profile.log");
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

if ($shouldPrint) {
	my $sth = $dbh->prepare("
	SELECT a.rule, a.type, a.rewrites, 
		a.matches, a.fragment, a.initialTries, 
		a.resolveTries,	a.successes, a.failures
	FROM data a
	WHERE a.type != 'op'
	--- ORDER BY a.matches DESC
	") or die $dbh->errstr;
	$sth->execute();
	print "Rule, Type, Rewrites, Matches, Fragment, Initial Tries, Resolve Tries, Successes, Failures\n";
	while (my $hash_ref = $sth->fetchrow_hashref) {
		my $rule = substr($hash_ref->{rule}, 0, $RULE_LENGTH);
		$rule =~ tr{\n}{ }; # turn newlines into spaces
		$rule =~ s/["]/""/g; # escape quotes
		my $type = $hash_ref->{type};
		my $rewrites = $hash_ref->{rewrites};
		my $matches = $hash_ref->{matches};
		my $fragment = $hash_ref->{fragment};
		my $initialTries = $hash_ref->{initialTries};
		my $resolveTries = $hash_ref->{resolveTries};
		my $successes = $hash_ref->{successes};
		my $failures = $hash_ref->{failures};
		print "\"$rule\", $type, $rewrites, $matches, $fragment, $initialTries, $resolveTries, $successes, $failures\n";
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
		my $sql = "INSERT INTO data (rule, type, rewrites, matches) VALUES (?, ?, ?, ?)";
		my $sth = $dbh->prepare($sql);
		my $retval = $sth->execute($rule, 'op', $rewrites, $rewrites);
		if (!$retval) {
			$sql = "UPDATE data SET rewrites = rewrites + ?, matches = matches + ? where rule = ? AND type = ?";
			$sth = $dbh->prepare($sql);
			$sth->execute($rewrites, $rewrites, $rule, 'op');
		}
		return;
	}
}
sub handleEq {
	my ($line, $file, $type) = @_;
	my $rule = $line;
	while (<$file>){
		$line = $_;
		chomp($line);
		if ($line =~ m/^rewrites: (\d+) \(/){
			my $rewrites = $1;
			my $sql = "INSERT INTO data (rule, type, rewrites, matches) VALUES (?, ?, ?, ?)";
			my $sth = $dbh->prepare($sql);
			my $retval = $sth->execute($rule, $type, $rewrites, $rewrites);
			if (!$retval) {
				$sql = "UPDATE data SET rewrites = rewrites + ?, matches = matches + ? where rule = ? AND type = ?";
				$sth = $dbh->prepare($sql);
				$sth->execute($rewrites, $rewrites, $rule, $type);
			}
			return;
		} if ($line =~ m/[\[ ]label ([^ ]+)[\] ]/){ # labeled equation
			$rule = $1;
			# print "$1\n"
		} else {
			$rule .= "$line\n";
		}
	}
}
sub handleCeq {
	my ($line, $file, $type) = @_;
	my $rule = $line;
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
			
			my $sql = "INSERT INTO data (rule, type, rewrites, matches, fragment, initialTries, resolveTries, successes, failures) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)";
			my $sth = $dbh->prepare($sql);
			my $retval = $sth->execute($rule, $type, $rewrites, $matches, $fragment, $initialTries, $resolveTries, $successes, $failures);
			if (!$retval) {
				$sql = "UPDATE data SET rewrites = rewrites + ?, matches = matches + ?, fragment = fragment + ?, initialTries = initialTries + ?, resolveTries = resolveTries + ?, successes = successes + ?, failures = failures + ? where rule = ? AND type = ?";
				$sth = $dbh->prepare($sql);
				$sth->execute($rewrites, $matches, $fragment, $initialTries, $resolveTries, $successes, $failures, $rule, $type);
			}
			return;
		} if ($line =~ m/[\[ ]label ([^ ]+)[\] ]/){ # labeled equation
			$rule = $1;
			# print "$1\n"
		} else {
			$rule .= "$line\n";
		}
	}
}

