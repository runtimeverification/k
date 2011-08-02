

kmod ISSUE062 is 

	
	syntax Exp ::= #Int
               | ! Exp
               | ? Exp

	rule ! 1 => ? 2
	rule ? 2 => 3

endkm
