
kmod ISSUE is
	including K
	syntax K ::= String
	syntax K ::= test1 | test2 | done
	syntax K ::= str ( String )
	define test1 => str("file://" +String "foo") [structural]
	define str("file://foo") => done [structural]
endkm
