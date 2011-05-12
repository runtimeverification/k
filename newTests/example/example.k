
kmod ISSUE is
	including K 
	including K-CONTEXTS 
	including K-PROPER
	syntax K ::= test1 | test2
	rule test1 => 'SomeLabel(.List{K}) [structural]
	rule test2 => 'SomeLabel(.List{K}) [structural]
endkm
