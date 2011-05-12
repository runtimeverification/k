
kmod ISSUE is
	including K 
	including K-CONTEXTS 
	including K-PROPER
	including PL-BUILTINS
	
	ops foo1 foo2 : -> K
	
	configuration 
		<T> 
			<threads>
				<thread multiplicity="*">
					<control>
						<k> .K </k>
					</control>
				</thread>
			</threads>
		</T>

	ops start1 start2 : -> Bag
	ops finish1 finish2 : -> Bag
	
	
	rule start1 => 
		<T>
			<threads>
				<thread>
					<control>
						<k> foo1 </k>
					</control>
				</thread>
			</threads>
		</T>
	
	rule start2 => 
		<T>
			<threads>
				<thread>
					<control>
						<k> foo2 </k>
					</control>
				</thread>
				<thread>
					<control>
						<k> foo2 </k>
					</control>
				</thread>
			</threads>
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
