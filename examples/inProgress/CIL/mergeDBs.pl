use strict;
use DBI;
my $RULE_LENGTH = 180;
my $numArgs = $#ARGV + 1;
# terrible hack :(
my $dbh = DBI->connect("dbi:SQLite:dbname=mytests.sqlite","","");
my $dbhTarget = DBI->connect("dbi:SQLite:dbname=gcc.sqlite","","");

# my $sth = $dbhTarget->prepare("
# ALTER TABLE data
# ADD COLUMN suite NULL DEFAULT 'gcc'
# ") or die $dbh->errstr;
# $sth->execute();

my $target = $dbhTarget->prepare("
INSERT INTO data (file, rule, type, kind, rewrites, matches, suite) VALUES (?, ?, ?, ?, ?, ?, 'mine')
");

my $sth = $dbh->prepare("
SELECT *
FROM data a
WHERE a.type != 'op'
") or die $dbh->errstr;
$sth->execute();
# Fragment, Initial Tries, Resolve Tries, 
print "Rule, Count, Kind, Matches, Rewrites\n";
while (my $hash_ref = $sth->fetchrow_hashref) {
	# my $rule = substr($hash_ref->{rule}, 0, $RULE_LENGTH);
	# $rule =~ tr{\n}{ }; # turn newlines into spaces
	# $rule =~ s/["]/""/g; # escape quotes
	# # my $file = $hash_ref->{file};
	# # my $type = $hash_ref->{type};
	# my $count = $hash_ref->{count};
	# my $kind = $hash_ref->{kind};
	# my $rewrites = $hash_ref->{rewrites};
	# my $matches = $hash_ref->{matches};
	# my $fragment = $hash_ref->{fragment};
	# my $initialTries = $hash_ref->{initialTries};
	# my $resolveTries = $hash_ref->{resolveTries};
	# my $successes = $hash_ref->{successes};
	# my $failures = $hash_ref->{failures};
	# print "\"$rule\"\n";
	# print "$count\n";
	# $fragment, $initialTries, $resolveTries, 
	$target->execute($hash_ref->{file}, $hash_ref->{rule}, $hash_ref->{type}, $hash_ref->{kind}, $hash_ref->{rewrites}, $hash_ref->{matches});
}
$dbh->disconnect();


# my $sth = $dbh->prepare("
# SELECT count(distinct a.rule) as count
# FROM data a
# WHERE a.type != 'op'
	# AND a.kind != 'macro'
# ") or die $dbh->errstr;
# $sth->execute();
# # Fragment, Initial Tries, Resolve Tries, 
# print "Rule, Count, Kind, Matches, Rewrites\n";
# while (my $hash_ref = $sth->fetchrow_hashref) {
	# my $rule = substr($hash_ref->{rule}, 0, $RULE_LENGTH);
	# $rule =~ tr{\n}{ }; # turn newlines into spaces
	# $rule =~ s/["]/""/g; # escape quotes
	# # my $file = $hash_ref->{file};
	# # my $type = $hash_ref->{type};
	# my $count = $hash_ref->{count};
	# # my $kind = $hash_ref->{kind};
	# # my $rewrites = $hash_ref->{rewrites};
	# # my $matches = $hash_ref->{matches};
	# # my $fragment = $hash_ref->{fragment};
	# # my $initialTries = $hash_ref->{initialTries};
	# # my $resolveTries = $hash_ref->{resolveTries};
	# # my $successes = $hash_ref->{successes};
	# # my $failures = $hash_ref->{failures};
	# # print "\"$rule\"\n";
	# print "$count\n";
	# # $fragment, $initialTries, $resolveTries, 
# }
# $dbh->disconnect();
