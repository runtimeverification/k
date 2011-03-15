in ../../k-prelude
kmod ISSUE is
	including K 
	including K-CONTEXTS 
	including K-PROPER
	including PL-BUILTINS
	
	ops foo1 foo2 : -> K
	
	configuration 
		<T> 
			<thread multiplicity="*">
				<k> .K </k>
			</thread>
		</T>

	ops start1 start2 : -> Bag
	ops finish1 finish2 : -> Bag
	
	
	rule start1 => 
		<T>
			<thread>
				<k> foo1 </k>
			</thread>
		</T>
	
	rule start2 => 
		<T>
			<thread>
				<k> foo2 </k>
			</thread>
			<thread>
				<k> foo2 </k>
			</thread>
		</T>
	
	rule [rule1]:
		< T >...
			< k > foo1 </ k >
		...</ T >	
		=> finish1
	
	rule [rule2]:
		< T >...
			< k > foo2 </ k >
			< k > foo2 </ k >
		...</ T >
		=> finish2
endkm
