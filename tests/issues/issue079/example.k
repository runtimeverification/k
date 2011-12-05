
module COMMON 
	
	syntax Bag ::= "test"
				| "eval" K

	syntax K ::= "foo"
				| "bar"
	
	configuration 
		<k> .K </k>
		<cell multiplicity="*"> .Bag </cell>
	
	macro test = eval(foo)

	rule 
		<k> foo => bar </k>
		(.Bag => <cell>... .Bag ...</cell>)
end module
