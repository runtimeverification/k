module ISSUE imports #META-LEVEL
	syntax K ::= "test1" | "test2" | "test3"
	rule test1 => test2 [transition]
	rule test1 => test3 [transition]
        
        syntax K ::= "test" "(" #Nat ")"
        rule test(N) => downTerm(getTermRT(metaSearch(upModule('ISSUE, false), upTerm(test1), 'R:K, nil, '*, unbounded, N:#Nat)),.K) 

end module
