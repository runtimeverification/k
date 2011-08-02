
kmod ISSUE is
	including K
	
	syntax KResult ::= #Nat | #Int // it's necessary to include ints AND nats
	
	syntax K ::= test1
	
	syntax K ::= collapse ( Bag )
	syntax K ::= bar
	
	syntax K ::= foo ( #Nat , K ) // change Nat to K and it works
	context foo(?:#Nat, `[HOLE`]:K)
		
	rule test1 => collapse(<k> foo(5, bar) </k>) [structural]
	rule collapse(<k>foo(N:#Nat, N:#Nat)</k>) => 31337 [structural]
	
	rule <k> bar => 5 ...</k> [structural]
endkm
