

kmod ISSUE062 is including K + PL-INT + PL-ID

	
	syntax Exp ::= Int
               | ! Exp
               | ? Exp

	rule ! 1 => ? 2
	rule ? 2 => 3

endkm
