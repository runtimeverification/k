# utils


# comments
our $comment = join("|", (
    "\\/\\/.*?\n",
    "\\/\\*.*?\\*\\/",
    "---\\(.*?---\\)",
    "---.*?\n",
    "\\*\\*\\*\\(.*?\\*\\*\\*\\)",
    "\\*\\*\\*.*?\n" ));




# returns file content as string
sub get_file_content
{
    my $filename = shift;
    
    open FILEHANDLE, "<", $filename or die "Could not open $filename:\n$!";
    my @input = <FILEHANDLE>;
    close FILEHANDLE;
    
    return join("", @input);
}

# sorts an array by length of its elements
sub length_sort
{
    sort {length $a <=> length $b} @_;
}

# get set-like array from another array
# get rid of duplicates
sub set
{
    if (@_)
    {
	my %map = map { $_ => 1 } @_;
	return keys %map;
    }
    
    ();
}
