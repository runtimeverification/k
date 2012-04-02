
module ISSUE
	syntax K ::= String
	syntax K ::= "test1" | "test2" | "done"
	declare str : String -> K 
	define test1 => str("file://" +String "foo") [structural]
	define str("file://foo") => done [structural]
end module
