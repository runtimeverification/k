module ISSUE 
	syntax K ::= test1 | test2
	syntax K ::= K "^" K
	tags anywhere
	rule test1 => '_^_(test2,, test2) [structural anywhere]
end module
