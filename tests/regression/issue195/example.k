module OTHERMODULE
	syntax K ::= foo-foo
	syntax K ::= bar
end module

module ISSUE imports OTHERMODULE
	syntax K ::= test
	
	define test => 'foo-foo(.List{K}) [structural]
	define ('foo-foo => 'bar)(.List{K}) [structural]
end module
