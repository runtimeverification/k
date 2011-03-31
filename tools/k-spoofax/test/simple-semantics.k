kmod SIMPLE-UNTYPED-SEMANTICS is
	configuration
	<T color="red">
		<threads color="orange">
			<thread multiplicity="*" color="yellow">
			<k color="green"> .K </k>
			<fstack color="blue"> .List </fstack>
			<xstack color="purple"> .List </xstack>
			<env color="violet"> .Map </env>
			<holds color="black"> .Map </holds>
			</thread>
		</threads>
		<genv color="pink"> .Map </genv>
		<store color="white"> .Map </store>
		<busy color="cyan"> .Set </busy>
		<in color="magenta"> .List </in>
		<out color="brown"> .List </out>
		<nextLoc color="gray"> 0 </nextLoc>
	</T>
	
	//@ \subsection*{Variable declaration}
	context `var ~X = ~[];
	rule <k> `var ~X:Id = ~V; => .K <_/k>
		<env> Env:Map => Env[L:Nat/X] </env>
		<store_> .K => L|->V <_/store>
		<nextLoc> L => 'sNat(L) </nextLoc>
		
	//@ \subsection*{Array declaration}
	context `var ~X[~_, ~[]:Exp, ~_];
	rule <k> `var ~X[~N:Nat]; => .K <_/k>
		<env> Env => Env[L/X] </env>
		<store_> .Map => (L |-> 'array('sNat(L), N)) '..('sNat(L), 'sNat('+Nat(L, N))) |-> 0 <_/store>
		<nextLoc> L => 'sNat('+Nat(L, N)) </nextLoc>
 

	rule `~I1 * ~I2 => '*Int(I1, I2) 
 	rule <k> X:Id => V:Val <_/k> <env_> X|->L <_/env> <store_> L|->V <_/store>
	
endkm