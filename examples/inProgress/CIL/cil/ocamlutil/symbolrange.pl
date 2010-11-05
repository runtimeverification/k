#!/usr/bin/perl


use Getopt::Long 2.17;

my $debug = 0;
my $file = "";

sub pdebug { 
    if($debug) { print STDERR @_; }
}

sub objdump {
    my ($cmd) = @_;
    my $base = "objdump $file --section=.text";
    &pdebug("Running: $base $cmd\n");
    open(IN, "$base $cmd |") 
        || die "Cannot run $base $cmd";
    my @lines = <IN>;
    close(IN);
    return @lines;
}

sub hextodec {
    my($h) = @_;
    my $v = 0;
    my $l = length($h);
    for(my $i=0;$i<$l;$i++) {
        my $c = substr($h, $i, 1);
        my $cval;
        if(ord($c) >= ord('0') && ord($c) <= ord('9')) {
            $cval = $c - '0';
        } elsif(ord($c) >= ord('a') && ord($c) <= ord('f')) {
            $cval = 10 + (ord($c) - ord('a'));
        } elsif($c >= 'A' && $c <= 'F') {
            $cval = 10 + ($c - 'A');
        } else {
            die "Invalid character $c in hex string $h";
        }
        $v = $v * 16 + $cval;
    }
    return $v;
}

sub dectohex {
    my($d) = @_;
    my $r = "";
    if($d == 0) { return "0x0"; }
    while($d > 0) {
        my $q = int($d / 16);
        my $rem = $d - 16 * $q;
        if($rem <= 9) {
            $r = $rem . $r;
        } else {
            $r = chr(ord('a') + $rem - 10) . $r;
        }
        $d = $q;
    }
    return "0x$r";
}

my $textvma;
my $text_section_idx;
my $fileformat;

sub parseTextSymbol {
    my ($l) = @_;
    my $name;
    my $vma;
    if($fileformat eq "pei-i386" && $l =~ m|.*\s+0x(\S+)\s+(\S+)$|) {
        $name = $2;
        $vma = $textvma + &hextodec($1);
    } elsif($fileformat eq "elf32-i386" && 
            $l =~ m|^\s*(\S*)\s.*\s\.text\s+\S+\s+(\S+)$|) {
        $name = $2;
        $vma = &hextodec($1);
    }
    &pdebug("parseTextSymbol:$l  name=$name, vma=".&dectohex($vma)."\n");
    return ($name, $vma);
}

my %options = 
    ("debug!"   => \$debug,
     "file=s"   => \$file,
     );


&GetOptions(%options);

# Get the file type
foreach my $l (&objdump("-f | grep 'file format'")) {
    if($l =~ m|.*\s(\S+)\s*$|) {
        $fileformat = $1;
    }
}
if(! defined($fileformat)) {
    die "Cannot find the file format";
}
&pdebug("File format is $fileformat\n");

# Get the parameters of the .text section
my $textoffset;
foreach my $l (&objdump("-h | grep .text")) {
    my @line = split(/\s+/, $l);
    while($line[0] eq '') {
        shift @line;
    }
    &pdebug("Parsing .text info: line=", join(':', @line), "\n");
    if($fileformat eq "pei-i386" && $line[1] eq ".text") {
        $text_section_idx = 1 + $line[0];
        $textoffset = &hextodec($line[5]);
        $textvma = &hextodec($line[3]);
        last;
    } elsif($fileformat eq "elf32-i386" && $line[1] eq ".text") {
        $text_section_idx = 0;
        $textoffset = &hextodec($line[5]);
        $textvma = &hextodec($line[3]);
        last;
    } else {
        die "Found unexpected output for -h: $l";
    }
}

&pdebug(".text section is at index $text_section_idx, offset $textoffset (" . &dectohex($textoffset) .
        ") and VMA=$textvma (" . &dectohex($textvma) . ")\n");

# Now load all the symbols
my %symbols = (); # Indexed by their name

# Construct here the grep expression for the diffent architectures
my $grep;
if($fileformat eq "pei-i386") {
    $grep = "sec  $text_section_idx";
} elsif($fileformat eq "elf32-i386") {
    $grep = '\.text';
} else {
    die "";
}
my @lines = &objdump("--syms | grep \"$grep\"");
# Get the one we care about
foreach my $l (@lines) {
    my ($name, $vma) = &parseTextSymbol($l);
    if(defined $name) { 
        # Insert it into the array of symbols
        $symbols{$name} = $vma;
    }
}

# Now sort the symbols by the VMA
my @symbolnames = sort { $symbols{$a} <=> $symbols{$b} } (keys %symbols);

# For each function that we got as argument produce its range of VMA
my %functions = ();
foreach my $f (@ARGV) { $functions{$f} = ""; }

for(my $i=0;$i<@symbolnames;$i++) {
    &pdebug("Found symbol $symbolnames[$i] at ". 
            &dectohex($symbols{$symbolnames[$i]})."\n");
    # See if the symbolname matches the start of a function that we must print
    foreach my $f (@ARGV) {
        if($symbolnames[$i]=~ m|^$f|) {
            $functions{$f} = $symbolnames[$i] . "," . $functions{$f};
            print STDERR "Found symbol $symbolnames[$i]\n";

            # A function we care about
            my $start = $symbols{$symbolnames[$i]};
            my $end;
            if($i + 1 < @symbolnames) { 
                $end = $symbols{$symbolnames[$i + 1]}
            } else {
                die "Not implemented: the last function";
            }
            $functions{$symbolnames[$i]} = 1;
            print $start, "-", $end, " ";
        }
    }
}

foreach my $f (keys %functions) {
    if($functions{$f} eq '') {
        warn "Warning: Could not find the range for function $f\n";
    }
}
