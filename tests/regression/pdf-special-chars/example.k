module ISSUE 
	syntax K ::= test1 | test2
	syntax K ::= K "^" K
	syntax K ::= K "%" K
	syntax K ::= K "$" K
	syntax K ::= K "&" K
	syntax K ::= K "\\" K
	syntax K ::= K "\\x" K
	syntax K ::= K "~x" K
	syntax K ::= K "~" K
	syntax K ::= K "[" K
	syntax K ::= K "]" K
	syntax K ::= K "{" K
	syntax K ::= K "}" K
	syntax K ::= K "#" K
	syntax K ::= K "{foo}" K
	syntax K ::= K "[foo]" K
end module
