in ../../k-prelude
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
		
	// this rule compiles, but doesn't match since test1 doesn't expand properly
	rule
		< k > foo1 => bar ...</ k >
		< staticSemantics >...
			< translationUnits > .Bag </ translationUnits >
		...</ staticSemantics >
		[structural]

	rule [terminate]:
		<T>...
			< k > bar ...</ k >
		...</T> => success
		[structural]
	
	
	// this should expand to include staticSemantics
	syntax Bag ::= test1
	rule test1 =>
		<T>... <staticSemantics>... .Bag ...</staticSemantics> ...</T>
		
endkm
