in ../../k-prelude
kmod ISSUE is
	including K 
	including K-CONTEXTS 
	including K-PROPER
	syntax K ::= test
	syntax K ::= foo String
	syntax K ::= String
	
	rule test => foo "bar 'char" [structural]
endkm
