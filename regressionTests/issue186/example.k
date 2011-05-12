
kmod ISSUE is
	including K 
	including K-CONTEXTS 
	including K-PROPER
	syntax K ::= test1 | test2 | test3 | test4 | test5 | test6
	rule [labeled-rule]:
		test1 => 'SomeLabel(.List{K}) 
	rule [labeled-large]:
		test2 => 'SomeLabel(.List{K})
	rule [labeled-op]:
		test3 => 'SomeLabel(.List{K})
	rule [labeled-syntax]:
		test4 => 'SomeLabel(.List{K}) 
	rule [labeled-macro]:
		test5 => 'SomeLabel(.List{K})
	rule [labeled-context]:
		test6 => 'SomeLabel(.List{K})
	[structural]

endkm
