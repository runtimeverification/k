
module ISSUE
	
	syntax KResult ::= Nat | Int // it's necessary to include ints AND nats
	
	declare test1 : -> K
	
	declare collapse : Bag -> K
	syntax K ::= bar
	
	syntax K ::= foo ( Nat , K ) // change Nat to K and it works
	context foo(?:Nat, HOLE)
		
	define test1 => collapse(<k> foo(5, bar) </k>)
	define collapse(<k>foo(N:Nat, N:Nat)</k>) => 31337
	
	rule <k> bar => 5 ...</k> [structural]
end module
