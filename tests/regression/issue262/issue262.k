module ISSUE262

syntax Exp ::= Val

syntax Val ::= Id
             | "\\" Id "." Exp
	     
end module
