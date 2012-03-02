kmod OTHERMODULE is
	including K
	syntax K ::= foo-foo
	syntax K ::= bar
endkm
kmod ISSUE is
	including OTHERMODULE
	
	syntax K ::= test
	
	define test => 'foo-foo(.List{K}) [structural]
	define ('foo-foo => 'bar)(.List{K}) [structural]
endkm
