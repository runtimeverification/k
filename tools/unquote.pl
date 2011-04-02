use strict;

# unquote maude metadata in order to speedup the tool
sub unquote {
	require XML::LibXML::Reader;
	
    my ($inputFile) = (@_);

	my $reader = new XML::LibXML::Reader(location => $inputFile) or die "cannot read $inputFile\n";

	$reader->read;

	if (! $reader->name eq "maudeml") {
		die "XML: Expected first entry to be 'maudeml'.";
	}

	$reader->nextElement('result');
	if ($reader->name eq "result") {
		$reader->nextElement;
		return getResult($reader) . "\n";
	} else {
		die "XML: Expected to find a result.";
	}
}
#####################################################################

sub getResult {
	my ($reader) = (@_);
	my $op = $reader->getAttribute('op');
	my $sort = $reader->getAttribute('sort');
	if (! defined($op) or ! defined($sort)){
		printf "%d %d %s %d\n", ($reader->depth, $reader->nodeType, $reader->name, $reader->isEmptyElement);
		die "XML: Found term without op or sort.";
	}
	if ($sort =~ /^(Qid|String|Sort|Variable|Constant|Term|NeTermList|GroundTerm|NeGroundTermList)$/) {
		return getTerm($reader, $op, $sort);
	} else {
		return getMeta($reader, $op, $sort);
	}
}

sub getTerm {
	my ($reader, $op, $sort) = (@_);
	if ($sort =~ /^(String)$/) {
		return $op;
	} elsif ($sort =~ /^(Qid|Sort|Variable)$/) {
		return getNormalThing($op);
	} elsif ($sort =~ /^Constant$/) {
		return getConstantThing($op);
	} elsif ($sort =~ /^(Term|GroundTerm)$/) { # |GroundTerm|NeGroundTermList|NeTermList
		return getNormalTerm($reader, $op, $sort);
	} elsif ($sort =~ /^(NeGroundTermList|NeTermList)$/) { # |GroundTerm|
		return getArgumentList($reader, $op, $sort);
	} else {
		die "unhandled sort: $sort\n";
	}
}

sub getNormalThing {
	my ($op) = (@_);
	
	return unquoteTerm($op);
}

sub getNormalTerm {
	my ($reader, $op, $sort) = (@_);

	if ($reader->isEmptyElement) {
		die "shouldn't be empty terms\n";
	}
	my @arguments = ();
	$reader->nextElement; # move to the first child
	my $oper = getResult($reader);
	$reader->nextSiblingElement;
	my $arguments = getResult($reader);
	$reader->nextSiblingElement;
	
	return "$oper($arguments)";
}

sub getArgumentList {
	my ($reader, $op, $sort) = (@_);
	
	my @arguments = ();
	$reader->nextElement; # move to the first child
	do {
		push(@arguments, getResult($reader));
	} while ($reader->nextSiblingElement);
	
	return join(', ', @arguments);
}

sub getConstantThing {
	my ($op) = (@_);
	
	if ($op =~ s/^'(.*)(\..*?)$/\($1\)$2/) {
		return $op;
	} else {
		die "couldn't handle op: $op";
	}
}

sub unquoteTerm {
	my ($term) = (@_);
	return substr($term, 1);
}

sub unBacktick {
	my ($term) = (@_);
	$term =~ s/\`([,\[\]\(\)\{\}])/$1/g;
	return $term;
}

sub getMeta {
	my ($reader, $op, $sort) = (@_);
	
	$op = unBacktick($op);
	
	if ($reader->isEmptyElement) {
		if ($sort =~ m/^(SubsortDeclSet|MembAxSet|TypeList|RuleSet|EquationSet)$/) {
			return "";
		}
		return $reader->getAttribute('op');
	}
	
	my @arguments = ();
	$reader->nextElement; # move to the first child
	do {
		push(@arguments, getResult($reader));
	} while ($reader->nextSiblingElement);
	
	if ($sort =~ m/^(Equation|OpDecl)$/) {
		if ($arguments[-1] eq "none") {
			pop(@arguments);
			$op =~ s/\[_\]//;
		}
	}
	
	if ($sort =~ m/^(SubsortDeclSet|ImportList|OpDeclSet|MembAxSet|EquationSet|NeTypeList|RuleSet)$/) {
		return join(' ', @arguments);
	}
	
	my @operator = split(/_/, $op, -1); # -1 to allow trailing fields
	
	if (abs($#operator - $#arguments) > 1) {
		die "XML: Underscores and arguments don't match on $op : $#operator , $#arguments";
	}
	# trick from http://stackoverflow.com/questions/38345/is-there-an-elegant-zip-to-interleave-two-lists-in-perl-5
	my @zipped = map {($operator[$_], (defined($arguments[$_])) ?  $arguments[$_] : "")} (0 .. $#operator);

	my $retval = join(' ', @zipped);
	if ($retval =~ m/\. $/) {
		$retval .= "\n";
	}
	return $retval;
}

1;