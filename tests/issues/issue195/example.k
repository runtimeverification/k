kmod OTHERMODULE is
	including K
	syntax K ::= foo-foo
	syntax K ::= bar
endkm
kmod ISSUE is
	including OTHERMODULE
	
	syntax K ::= test
	
	rule test => 'foo-foo(.List{K}) [structural]
	rule ('foo-foo => 'bar)(.List{K}) [structural]
endkm
