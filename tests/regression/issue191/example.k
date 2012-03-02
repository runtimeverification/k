
kmod ISSUE is
	syntax K ::= test1 | test2 | test3
	syntax K ::= foo #String
	syntax K ::= #String
	
	define test1 => foo "bar 'char" [structural]
	define test2 => foo "bar\"" [structural]
	rule test3 => foo "bar\"bim" [structural anywhere]
endkm
