
kmod ISSUE is
	including K
	syntax K ::= #String
	syntax K ::= test1 | test2 | done
	syntax K ::= str ( #String )
	rule test1 => str("file://" +String "foo") [structural]
	rule str("file://foo") => done [structural]
endkm
