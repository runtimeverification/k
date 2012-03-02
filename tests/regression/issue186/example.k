
kmod ISSUE is
	including K 
	including K-CONTEXTS 
	syntax K ::= test1 | test2 | test3 | test4 | test5 | test6
	define [labeled-rule]:
		test1 => 'SomeLabel(.List{K}) 
	define [labeled-large]:
		test2 => 'SomeLabel(.List{K})
	define [labeled-op]:
		test3 => 'SomeLabel(.List{K})
	define [labeled-syntax]:
		test4 => 'SomeLabel(.List{K}) 
	define [labeled-macro]:
		test5 => 'SomeLabel(.List{K})
	define [labeled-context]:
		test6 => 'SomeLabel(.List{K})
	[structural]

endkm
