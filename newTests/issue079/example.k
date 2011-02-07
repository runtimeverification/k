in ../../k-prelude
kmod COMMON is
	including K 
	including K-CONTEXTS 
	including K-PROPER
	
	syntax Bag ::= test
				| eval K

	syntax K ::= foo
				| bar
	
	configuration 
		< k > .K </ k >
		< cell * > .Bag </ cell * >
	
	macro test = eval(foo)

	rule 
		< k > foo => bar </ k >
		(.Bag => < cell >... .Bag ...</ cell >)
endkm
