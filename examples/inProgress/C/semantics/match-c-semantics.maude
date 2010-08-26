mod MATCH-C-SEMANTICS is
	including COMMON-C-SEMANTICS .

	subsort Annotation-Statement < K .

	--- [| 0,0,<config>
		--- <k> K </k>
		--- <env> .Env </env>
		--- <heap> .Heap </heap>
		--- <form> TrueFormula </form>
		--- <menv> .MatchEnv </menv>
		--- <newSym> 0 </newSym>
		--- <newImpl> 0 </newImpl>
	--- </config> |]
	
	op loc : -> Nat .
	op n : Nat -> Nat .
	
	eq eval(P:Program) = 
		< T >
			< Task >
				< k > P:Program </ k >
				< env > .Map </ env >
				< loopStack > .List </ loopStack >
				< locals > .Bag </ locals >
				< parameters > .Bag </ parameters >
				< types > .Map </ types >
				< output > "" </ output >
				< malloced > .Map </ malloced >
				< mem > .Map </ mem >
				< statics > .Map </ statics >
				---< form > TrueFormula </ form >
			</ Task >
			< todo > .K </ todo >
			< typedefs > .Map </ typedefs >
			< callStack > .List </ callStack >
			< nextLoc > n(0) </ nextLoc >
			< genv > .Map </ genv > 
			< gmem > .Map </ gmem > 
		</ T > .
		
	mb [function-declaration]: rule 
		< k > [
			Declaration(DS:TogetherList, Direct-Function-Declarator(I:Id, PTL:Parameter-Type-List)){
				B:TogetherList
			}
			=> .K]
		...</ k >
		< todo > [.K => I:Id] ...</ todo >
		< genv > [E:Map => E:Map[n(Loc:Nat) / I:Id]]  </ genv >
		< gmem > [M:Map => M:Map[Closure(Declaration(DS:TogetherList, Direct-Function-Declarator(I:Id, PTL:Parameter-Type-List)){ B:TogetherList }) / n(Loc:Nat)]] </ gmem >
		< nextLoc > [n(Loc:Nat) => n(sNat(Loc:Nat))] </ nextLoc >
		: KSentence .
		
	mb [move-pre-through-block]: rule
		['Block(annotation pre(C:Bag) ; ~> S:Statement) => annotation pre(C:Bag) ; ~> Block(S:Statement)]
	: KSentence [metadata "structural"] .
	mb [move-pre-through-declarations]: rule
		[Declaration(T:TogetherList, DL:Init-Declarator-List) ~> annotation pre(C:Bag) ; => annotation pre(C:Bag) ; ~> Declaration(T:TogetherList, DL:Init-Declarator-List)]
	: KSentence [metadata "structural"] .
	mb [move-post-through-all]: rule
		[annotation post(C:Bag) ; ~> K:NeK => K:NeK ~> annotation post(C:Bag) ;]
	: KSentence [metadata "structural"] .
	
	op absBind : K -> K .
	op i : Nat -> Int .
	op debug : -> K .
	
	--- sort Foo .
	--- sort List{Foo} .
	--- subsort Foo < List{Foo} < K .
	--- ops z x y : -> Foo .
	--- op .List{Foo} : -> List{Foo} .
	--- op _#_ : List{Foo} List{Foo} -> List{Foo} [assoc id: .List`{Foo`}] .
	
	--- op theTest : -> K .
	--- op Bar : List{Foo} -> K .
	--- eq theTest = Bar(z # x) .
	
	--- op theTest2 : -> K .
	--- eq theTest2 = Bar(z) .
	
	--- mb rule [Bar(F:Foo # L:List{Foo}) => Bar(L:List{Foo})] : KSentence .
	
	mb rule [Parameter-Declaration(void) => .List{Parameter}] : KSentence .
	
	mb [absBind-done]: rule
		< k > [absBind(Parameter-Type-List(.List{Parameter})) => .K] ...</ k > 
	: KSentence .
	

	--- mb [absBind-one]: rule
		--- < k > [absBind(Parameter-Type-List(Parameter-Declaration(int, I:Id) ,., P:List{Parameter})) => absBind(Parameter-Type-List(P:List{Parameter}))] ...</ k > 
		--- < env >... [.Map => I:Id |-> n(Loc:Nat)] ...</ env >
		--- < mem >... [.Map => n(Loc:Nat) |-> n(sNat(Loc:Nat))] ...</ mem >
		--- < nextLoc > [n(Loc:Nat) => n(Loc:Nat +Nat 2)] </ nextLoc >
	--- : KSentence .
	
	
	--- < k > [bind((V:Value .,. L:List{Expression}),, 
				--- Parameter-Type-List(Parameter-Declaration(int, I:Id) ,., P:List{Parameter})) =>
			--- bind((.List{Expression} .,. L:List{Expression}),, 
				--- Parameter-Type-List(.List{Parameter} ,., P:List{Parameter}))]
				--- ...</ k > 
		--- < env >... [.Map => I:Id |-> Loc:Nat] ...</ env >
		--- < mem >... [.Map => Loc:Nat |-> V:Value] ...</ mem >
		--- < parameters >... [.Bag => Bag(Parameter-Declaration(int, I:Id))] ...</ parameters >
		--- < nextLoc > [Loc:Nat => sNat(Loc:Nat)] </ nextLoc >
	
	--- mb [create-task]: rule
		--- < Task > 
			--- < k > .K </ k > 			
			--- < mem > Loc:Nat |-> Closure(Declaration(DS:TogetherList, Direct-Function-Declarator(I:Id, PTL:Parameter-Type-List)){ B:TogetherList }) M:Map </ mem >
			--- C:Bag 
		--- </ Task >
		--- < todo > [I:Id => .K] ...</ todo >
		--- [.Bag => 
			--- < Task > 
				--- < k > absBind(PTL:Parameter-Type-List) ~> B:TogetherList </ k > 
				
				--- < mem > Loc:Nat |-> Closure(Declaration(DS:TogetherList, Direct-Function-Declarator(I:Id, PTL:Parameter-Type-List)){ B:TogetherList }) M:Map </ mem >
				--- C:Bag 
			--- </ Task >
		--- ]
		--- < genv >... I:Id |-> Loc:Nat ...</ genv >
	--- : KSentence .
	
	
	--- mb [task-done]: rule 
		--- [< Task >... < k > .K </ k > < form > TrueFormula </ form > ...</ Task >
		--- =>
		--- .Bag]
		--- : KSentence .
		
		
	
endm
