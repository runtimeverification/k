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
	context var ~X = ~[];
	rule <k> var ~X:Id = ~V; => .K ...</k>
		<env> Env:Map => Env[L:Nat/X] </env>
		<store>... .K => L |-> V ...</store>
		<nextLoc> L => sNat(L) </nextLoc>
		
	//@ \subsection*{Array declaration}
	context var ~X[~_, ~[]:Exp, ~_];
	rule <k> var ~X[~N:Nat]; => .K ...</k>
		<env> Env => Env[L / X] </env>
		<store>... .Map => (L |-> 'array(sNat(L), N)) '..(sNat(L), sNat(L +Nat N)) |-> 0 ...</store>
		<nextLoc> L => sNat(L +Nat N) </nextLoc>

	/*@ The rule below lazily handles multi-dimensional arrays through code generation.  
		The reason for handling it here than as a syntactic desugaring is that we want 
		to ensure the dimensions of the array are already evaluated before we generate 
		the code, to avoid strange behaviors for code like var a[++x,++x]; 
	*/
	// syntax Id ::= freshId ( Nat )
	rule 
		<k> var ~X[~N, ~N':Nat, ~Vl]; 
			=>	var ~X[~N];
				 for ~'freshId(L) = 0 to ~(N +Int -1) do {
				 	var ~'freshId(L +Nat 1)[~N', ~Vl];
				 	~X[~'freshId(L)] = ~'freshId(L +Nat 1);
				 }
		...</k>
		<nextLoc> L => L +Nat 2 </nextLoc>  



	rule ~I1 * ~I2 => I1 *Int I2 
 	rule <k> X:Id => V:Val ...</k> <env>... X |-> L ...</env> <store>... L |-> V ...</store>
	
endkm