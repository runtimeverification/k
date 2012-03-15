module ISSUE 

	configuration
		<k> .K </k>
		
	syntax K ::= test1 | test2 | done
	syntax K ::= "foo" "(" K ")" [strict]
	syntax KResult ::= res1 | res2
	syntax KLabel ::= "'mylabel" [hybrid]
	
	rule test1 => foo('mylabel(res1))
	rule test2 => foo('mylabel(res1,, res2))
	
	rule foo(V:KResult) => done
end module
