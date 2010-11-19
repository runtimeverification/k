use strict;
use DBI;
my $RULE_LENGTH = 300;
my $numArgs = $#ARGV + 1;
# terrible hack :(
my $dbh = DBI->connect("dbi:SQLite:dbname=gcc.sqlite","",""); #maudeProfileDBfile.sqlite
# {PrintError => 0}
if ($numArgs == 1) {
	my $flag = $ARGV[0];
	if ($flag eq "-labels") {
		printLabels(); exit 0;
	}
	if ($flag eq "-common") {
		# print "printing common rules\n";
		printCommonRules(); exit 0;
	}
	if ($flag eq "-c") {
		printFileInfo(); exit 0;
	}
	if ($flag eq "-p") {
		printData(); exit 0;
	}
	if ($flag eq "-lib") {
		printLib(); exit 0;
	}
	if ($flag eq "-count") {
		printCount(); exit 0;
	}
	if ($flag eq "-clean") {
		cleanDuplicates(); exit 0;
	}
	
}

$dbh->disconnect;

sub cleanDuplicates {
	$dbh->do("UPDATE data SET rule = replace(rule, '(T).CellLabel', 'T') WHERE rule like '%(T).CellLabel%'");
	$dbh->do("UPDATE data SET rule = replace(rule, '(k).CellLabel', 'k') WHERE rule like '%(k).CellLabel%'");
	$dbh->do("UPDATE data SET rule = replace(rule, '(type).CellLabel', 'type') WHERE rule like '%(type).CellLabel%'");
	$dbh->do("UPDATE data SET rule = replace(rule, '(env).CellLabel', 'env') WHERE rule like '%(env).CellLabel%'");
	$dbh->do("UPDATE data SET rule = replace(rule, '(buffer).CellLabel', 'buffer') WHERE rule like '%(buffer).CellLabel%'");
	$dbh->do("UPDATE data SET rule = replace(rule, '(mem).CellLabel', 'mem') WHERE rule like '%(mem).CellLabel%'");
	$dbh->disconnect();
}

sub printData {
	my $sth = $dbh->prepare("
	SELECT count(a.file) as count, a.rule, a.kind,
	sum(a.rewrites) as rewrites, SUM(a.matches) as matches
	FROM data a
	--- WHERE a.type != 'op' AND a.kind != 'macro'
	WHERE a.kind == 'macro' AND (
	a.rule LIKE '%structural%' or a.rule LIKE '%computational%')
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
		my $suite = $hash_ref->{suite};
		# my $fragment = $hash_ref->{fragment};
		# my $initialTries = $hash_ref->{initialTries};
		# my $resolveTries = $hash_ref->{resolveTries};
		# my $successes = $hash_ref->{successes};
		# my $failures = $hash_ref->{failures};
		print "$suite, \"$rule\", $count, $kind, $matches, $rewrites\n";
		# $fragment, $initialTries, $resolveTries, 
	}
	$dbh->disconnect();
}
sub printCount {
	my $sth = $dbh->prepare("
	SELECT count(distinct a.rule) as count
	FROM data a
	WHERE a.type != 'op'
	AND (a.kind != 'macro' 
	OR (a.kind == 'macro' AND (a.rule LIKE '%structural%' or a.rule LIKE '%computational%')))
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
		# my $kind = $hash_ref->{kind};
		# my $suite = $hash_ref->{suite};
		# my $rewrites = $hash_ref->{rewrites};
		# my $matches = $hash_ref->{matches};
		# my $fragment = $hash_ref->{fragment};
		# my $initialTries = $hash_ref->{initialTries};
		# my $resolveTries = $hash_ref->{resolveTries};
		# my $successes = $hash_ref->{successes};
		# my $failures = $hash_ref->{failures};
		# print "\"$rule\"\n";
		print "$count\n";
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
		--- AND suite == 'gcc'
		AND (a.kind != 'macro'
			OR (a.kind == 'macro' AND (a.rule LIKE '%structural%' or a.rule LIKE '%computational%'))
			)
		GROUP BY a.rule
	) b
	--- where b.count >= 50
	") or die $dbh->errstr;
	$sth->execute();
	# Fragment, Initial Tries, Resolve Tries, 
	# print "Rule\n";
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
sub printLabels {
# update data set rule = replace(rule, '(k).CellLabel', 'k')
	# --- SELECT replace(a.rule, '(k).CellLabel', 'k') as new
	# --- FROM data a
	# WHERE rule like '%(k).CellLabel%'
	# --- GROUP BY new
	my $sth = $dbh->prepare("
	SELECT rule 
	FROM data a
	WHERE rule like '%.CellLabel%'
	--- UPDATE data SET rule = replace(rule, '(T).CellLabel', 'T')
	--- WHERE rule like '%(T).CellLabel%'
	") or die $dbh->errstr;
	$sth->execute();
	# Fragment, Initial Tries, Resolve Tries, 
	print "Rule\n";
	while (my $hash_ref = $sth->fetchrow_hashref) {
		my $rule = substr($hash_ref->{rule}, 0, $RULE_LENGTH);
		$rule =~ tr{\n}{ }; # turn newlines into spaces
		$rule =~ s/["]/""/g; # escape quotes
		$rule = "\"$rule\"";
		# my $new = $hash_ref->{new};
		# my $rewrites = $hash_ref->{rewrites};
		print "$rule\n";
		# $fragment, $initialTries, $resolveTries, 
	}
	$dbh->disconnect();
}
sub printLib {
# update data set rule = replace(rule, '(k).CellLabel', 'k')
	# --- SELECT replace(a.rule, '(k).CellLabel', 'k') as new
	# --- FROM data a
	# WHERE rule like '%(k).CellLabel%'
	# --- GROUP BY new
	my $sth = $dbh->prepare("
	SELECT rule, file
	FROM data a
	WHERE rule like 'calloc%'
	--- UPDATE data SET rule = replace(rule, '(T).CellLabel', 'T')
	--- WHERE rule like '%(T).CellLabel%'
	") or die $dbh->errstr;
	$sth->execute();
	# Fragment, Initial Tries, Resolve Tries, 
	print "Rule\n";
	while (my $hash_ref = $sth->fetchrow_hashref) {
		my $rule = substr($hash_ref->{rule}, 0, $RULE_LENGTH);
		$rule =~ tr{\n}{ }; # turn newlines into spaces
		$rule =~ s/["]/""/g; # escape quotes
		$rule = "\"$rule\"";
		my $file = $hash_ref->{file};
		# my $rewrites = $hash_ref->{rewrites};
		print "$file, $rule\n";
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
