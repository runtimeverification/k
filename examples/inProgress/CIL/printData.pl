use strict;
use DBI;
my $RULE_LENGTH = 60;
my $numArgs = $#ARGV + 1;
# terrible hack :(
my $dbh = DBI->connect("dbi:SQLite:dbname=maudeProfileDBfile.sqlite","","");
# {PrintError => 0}
if ($numArgs == 1) {
	my $flag = $ARGV[0];
	if ($flag eq "-common") {
		print "printing common rules\n";
		printCommonRules(); exit 0;
	}
	if ($flag eq "-c") {
		printFileInfo(); exit 0;
	}
	if ($flag eq "-p") {
		printData(); exit 0;
	}
}

$dbh->disconnect;

sub printData {
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

sub printCommonRules {
	my $sth = $dbh->prepare("
	SELECT b.rule as rule, b.count as count, b.rewrites as rewrites
	from (SELECT a.rule, count(file) as count, sum(rewrites) as rewrites
		FROM data a
		WHERE a.type != 'op' 
			AND a.kind != 'macro'
			AND a.rewrites > 0
		GROUP BY a.rule
	) b
	--- where b.count >= 50
	") or die $dbh->errstr;
	$sth->execute();
	# Fragment, Initial Tries, Resolve Tries, 
	print "Rule\n";
	while (my $hash_ref = $sth->fetchrow_hashref) {
		my $rule = substr($hash_ref->{rule}, 0, $RULE_LENGTH);
		$rule =~ tr{\n}{ }; # turn newlines into spaces
		$rule =~ s/["]/""/g; # escape quotes
		$rule = "\"$rule\"";
		my $count = $hash_ref->{count};
		my $rewrites = $hash_ref->{rewrites};
		print "$rule, $count, $rewrites\n";
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
