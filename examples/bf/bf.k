
kmod BF is
	including K-PROPER
	including PL-INT
	including PL-STRING
	including K
--- Syntax
	op memory : -> CellLabel
	op output : -> CellLabel
	op result : -> CellLabel
	op input : -> CellLabel
	op k : -> CellLabel

	--- comments from http://en.wikipedia.org/wiki/Brainfuck
	op Seq : -> KProperLabel [metadata "arity 2"]
	op GoRight : -> KProperLabel [metadata "arity 0"] --- increment the data pointer (to point to the next cell to the right).
	op GoLeft : -> KProperLabel [metadata "arity 0"] --- decrement the data pointer (to point to the next cell to the left).
	op Increase : -> KProperLabel [metadata "arity 0"] --- increment (increase by one) the byte at the data pointer.
	op Decrease : -> KProperLabel [metadata "arity 0"] --- decrement (decrease by one) the byte at the data pointer.
	op Print : -> KProperLabel [metadata "arity 0"] --- output the value of the byte at the data pointer.
	op Read : -> KProperLabel [metadata "arity 0"] --- accept one byte of input, storing its value in the byte at the data pointer.
	op While : -> KProperLabel [metadata "arity 1"]
	--- [ 	if the byte at the data pointer is zero, then instead of moving 
	---		the instruction pointer forward to the next command, jump it 
	---		forward to the command after the matching ] command*.
	--- ] 	if the byte at the data pointer is nonzero, then instead of moving 
	---		the instruction pointer forward to the next command, jump it back 
	---		to the command after the matching [ command*.
	
--- Semantics
	op sentinel : -> KLabel
	op eval : K -> Bag
	op eval : K K -> Bag
	op inject : Int -> KResultLabel
	op inject : String -> KResultLabel
	
	--- helper functions.  can the basic ones be auto generated?
	op eightbit : -> KLabel
	rule 
		eightbit(inject(I:Int)(.List{K})) 
		=> inject((((I:Int %Int 256) +Int 256) %Int 256))(.List{K})
	
	op kcharString : -> KLabel
	rule 
		kcharString(inject(N:Nat)(.List{K})) 
		=> inject(charString(N:Nat))(.List{K})

	op +String : -> KLabel
	rule 
		+String(inject(S1:String)(.List{K}),, inject(S2:String)(.List{K})) 
		=> inject(S1:String +String S2:String)(.List{K})
		
	
	op firstChar : -> KProperLabel [arity 1]
	op butFirstChar : -> KProperLabel [arity 1]
	op charToAscii : -> KProperLabel [arity 1]
	
	rule [firstChar]:
		firstChar(inject(S:String)(.List{K})) => inject(substrString(S:String, 0, 1))(.List{K})
		 [structural]
	rule [charToAscii]: 
		charToAscii(inject(C:Char)(.List{K})) => inject(asciiString(C:Char))(.List{K})
		 [metadata "structural"]
	rule [butFirstChar]: 
		butFirstChar(inject(S:String)(.List{K})) => inject(substrString(S:String, 1, lengthString(S:String)))(.List{K})
		 [metadata "structural"]
	--- end helper functions
	
	configuration 
		< T >
			< k > K:K </ k >
			< memory > L:List </ memory >
			< output > K:K </ output >
			< input > K:K </ input >
		</ T >  
		< result > K:K </ result > 
		
	
	eq [Start]: eval(K:K) =
		< T >
			< k > K:K </ k >
			< memory > ListItem(sentinel(.List{K})) </ memory >
			< output > inject("")(.List{K}) </ output >
			< input > inject("")(.List{K}) </ input >
		</ T >
		
	eq [Start-With-Input]: eval(K:K, K':K) = 
		< T >
			< k > K:K </ k >
			< memory > ListItem(sentinel(.List{K})) </ memory >
			< output > inject("")(.List{K}) </ output >
			< input > K':K </ input >
		</ T >

	rule [Finish]: 
		< T > S:Bag < k > .K </ k > < output > K:K </ output > </ T > 
			=> < result > K:K </ result >
		  [metadata "structural"]
		
	rule
		< memory > ListItem(sentinel(.List{K})) => ListItem(inject(0)(.List{K})) ListItem(sentinel(.List{K})) ...</ memory > 
		 [metadata "structural"]
		
	rule [Sequence]: 
		Seq(K1:K,, K2:K) => K1:K ~> K2:K
		 [metadata "structural"]
		
	rule [Increase]: 
		< k > Increase(.List{K}) => .K ...</ k >
		< memory > ListItem((inject(I:Int)(.List{K}) => (inject(I:Int +Int 1))(.List{K}))) ...</ memory > 
		 [metadata "structural"]
	rule [Decrease]: 
		< k > Decrease(.List{K}) => .K ...</ k >
		< memory > ListItem((inject(I:Int)(.List{K}) => (inject(I:Int -Int 1))(.List{K}))) ...</ memory > 
		 [metadata "structural"]
	
	rule [WhileNZ-NZ]: 
		< k > While(K:K) => K:K ~> While(K:K) ...</ k > 
		< memory > ListItem(inject(I:Int)(.List{K})) ...</ memory > 
		if (I:Int =/=Bool 0) 
		 [metadata "structural"]
	rule [WhileNZ-Z]: 
		< k > While(K:K) => .K ...</ k >
		< memory > ListItem(inject(0)(.List{K})) ...</ memory > 
		 [metadata "structural"]
		
	rule [GoRight]: 
		< k > GoRight(.List{K}) => .K ...</ k > 
		< memory > Li:ListItem L:List => L:List Li:ListItem </ memory > 
		 [metadata "structural"]
	rule [GoLeft]: 
		< k > GoLeft(.List{K}) => .K ...</ k > 
		< memory > L:List Li:ListItem => Li:ListItem L:List </ memory > 
		 [metadata "structural"]
		
	rule [Output]: 
		< k > Print(.List{K}) => .K ...</ k > 
		< memory > ListItem(I:K) ...</ memory > 
		< output > S:K => +String(S:K,, kcharString(eightbit(I:K))) </ output > 
		 [metadata "structural"]
	rule [Input]: 
		< k > Read(.List{K}) => .K ...</ k >
		< memory > ListItem((inject(I:Int)(.List{K}) => charToAscii(firstChar(Input:K)))) ...</ memory > 
		< input > Input:K => butFirstChar(Input:K) </ input > 
		 [metadata "structural"]
endkm

