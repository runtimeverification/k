
kmod ISSUE is
	including K
	
	syntax K ::= test1 | test2
	rule test1 => 'SomeLabel(.List{K}) [structural]
	rule test2 => 'SomeLabel(.List{K})
endkm
