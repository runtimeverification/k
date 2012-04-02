module ISSUE 
	syntax KResult ::= t "(" Set "," K ")"
	syntax K ::= fromArray "(" Int "," Nat ")"
	syntax Bool ::= hasUnionMarker "(" KResult ")"
	
	syntax K ::= test1 | test2 | answer | foo | bar1 | bar2 | baz
	
	rule test1 => answer 
		when hasUnionMarker(bar1)
	rule bar1 => t(.Set, baz)
	
	rule test2 => answer 
		when hasUnionMarker(bar2)
	rule bar2 => t(SetItem(fromArray(0, 0)), baz)
	
	rule hasUnionMarker(t(.Set, ?)) => true
	rule hasUnionMarker(t(? (SetItem(_:K) => .Set), ?))
	
end module
