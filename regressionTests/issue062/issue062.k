in ../../k-prelude

kmod ISSUE062 is including K + PL-NAT + PL-ID

	
	syntax Exp ::= Int
               | ! Exp
               | ? Exp

	rule ! 1 => ? 2
	rule ? 2 => 3

endkm
