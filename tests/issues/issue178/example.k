
kmod ISSUE is
	including K 
	including K-CONTEXTS 
	including K-PROPER
	
	syntax K ::= foo1
	syntax K ::= foo2
	syntax K ::= bar
	syntax Bag ::= success
	
	configuration 
		<T>
			<k> foo1 </k>
			<staticSemantics multiplicity="?">
				<translationUnits> .Bag </translationUnits>
			</staticSemantics>
		</T>
		
	// this rule compiles
	rule
		< k > foo1 => bar ...</ k >
		< staticSemantics >...
			< translationUnits > .Bag </ translationUnits >
		...</ staticSemantics >
		[structural]
	
	// this rule fails to compile at all
	rule [broken]:
		< k > foo2 => bar ...</ k >
		(< staticSemantics >...
			< translationUnits > .Bag </ translationUnits >
		...</ staticSemantics >) => .Bag
		[structural]

	rule [terminate]:
		<T>...
			< k > bar ...</ k >
		...</T> => success
		[structural]
	
	
	syntax Bag ::= test1
	rule test1 =>
		<T> 
			<k> foo1 </k>
			<staticSemantics>
				<translationUnits> .Bag </translationUnits>
			</staticSemantics>
		</T>
		
	
	syntax Bag ::= test2
	rule test2 => 
		<T> 
			<k> foo2 </k>
			<staticSemantics>
				<translationUnits> .Bag </translationUnits>
			</staticSemantics>
		</T>
		
endkm
