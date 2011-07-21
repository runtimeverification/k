

kmod ISSUE062 is including K + #INT + #ID

	
	syntax Exp ::= Int
               | ! Exp
               | ? Exp

	rule ! 1 => ? 2
	rule ? 2 => 3

endkm
