
kmod ISSUE is
	including K
	
	syntax K ::= test1 
	eq test1 = 'SomeLabel(.List{K}) [owise]
	rule test1 => 'OtherLabel(.List{K}) [computational]
endkm
