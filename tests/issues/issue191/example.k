
kmod ISSUE is
	including K 
	including K-CONTEXTS 
	including K-PROPER
	syntax K ::= test1 | test2 | test3
	syntax K ::= foo String
	syntax K ::= String
	
	rule test1 => foo "bar 'char" [structural]
	// rule test2 => foo "bar\"" [structural]
	rule test3 => foo "bar\"bim" [structural]
endkm
