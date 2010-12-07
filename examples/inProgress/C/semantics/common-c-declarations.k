kmod COMMON-SEMANTICS-DECLARATIONS-INCLUDE is
	including COMMON-INCLUDE 
	op figureInitializer-aux : Id Type K -> K [metadata "strict(3)"] --- id, type, initializer
	op declarationObject : Type K K -> K --- type, translation unit it was defined in, definition
	
	op external : -> K 
	op internal : -> K 
	op noLinkage : -> K 
	
	op initializer : K -> KResult 
	op startInitializer : Type Id K -> K 
endkm

kmod COMMON-SEMANTICS-DECLARATIONS-BINDING is
	including COMMON-SEMANTICS-DECLARATIONS-INCLUDE 

	--- empty binding
	--- fixme not really a sequence point
	
	op bind-aux : Nat List{C} List{Type} -> K 
	rule
		< k > bind(L:List{C}, L':List{Type}) => bind-aux(NullPointer, L:List{C}, L':List{Type}) ...</ k > 
		[structural] 
	
	rule [bind-empty]:
		< k > bind-aux(?, Nil, typedDeclaration(void, ?)) => sequencePoint ...</ k > 
		[structural] 
	rule [bind-empty]:
		< k > bind-aux(?, Nil, Nil) => sequencePoint ...</ k > 
		[structural] 
		
		
	--- n1494 6.5.2.2:6 If the expression that denotes the called function has a type that does not include a prototype, the integer promotions are performed on each argument, and arguments that have type float are promoted to double. These are called the default argument promotions. If the number of arguments does not equal the number of parameters, the behavior is undefined. If the function is defined with a type that includes a prototype, and either the prototype ends with an ellipsis (, ...) or the types of the arguments after promotion are not compatible with the types of the parameters, the behavior is undefined. If the function is defined with a type that does not include a prototype, and the types of the arguments after promotion are not compatible with those of the parameters after promotion, the behavior is undefined, except for the following cases: 
	--- — one promoted type is a signed integer type, the other promoted type is the corresponding unsigned integer type, and the value is representable in both types;
	--- — both types are pointers to qualified or unqualified versions of a character type or void
	
	rule [bind-coerce-array]:
		bind-aux(?, L:List{C}, (?:List{Type} :: typedDeclaration((arrayType(T:Type, ?) => pointerType(T:Type)), X:Id) :: ?:List{Type}))
		[structural] 
	rule [bind-coerce-incompleteArray]:
		bind-aux(?, L:List{C}, (?:List{Type} :: typedDeclaration((incompleteArrayType(T:Type) => pointerType(T:Type)), X:Id) :: ?:List{Type}))
		[structural] 
		
	rule [bind-one]:
		< k > true ~> bind-aux(?, (tv(V:List{K}, T':Type) :: L:List{C}), (typedDeclaration(T:Type, X:Id) :: P:List{Type}))
			=> allocateType(Loc:Nat, T:Type)
			~> addToEnv(X:Id, Loc:Nat)
			~> giveType(X:Id, T:Type)
			~> initialize(X:Id, T:Type, Computation(X:Id := tv(V:List{K}, T':Type)))
			~> bind-aux(Loc:Nat, L:List{C}, P:List{Type}) 
		...</ k > 
		< nextLoc > Loc:Nat => inc(Loc:Nat) </ nextLoc >
		< localAddresses >... (.).Set => SetItem(Loc:Nat) ...</ localAddresses >
		if notBool hasArrayType(T:Type)
		[structural] 
		
	rule [bind-one]:
		< k > (. => isTypeCompatible(T:Type, T':Type)) ~> bind-aux(?, (tv(V:List{K}, T':Type) :: L:List{C}), (typedDeclaration(T:Type, X:Id) :: P:List{Type}))
		...</ k > 
		[structural] 
	
	op append : Nat Nat Value -> K
	rule [append-existing]:
		< k > append(sym(Block:Nat) +Nat 0, Len:Nat, V:Value) 
			=> write(sym(Block:Nat) +Nat OldLen:Nat, V:Value)
		...</ k >
		< mem >... Block:Nat |-> memblock((OldLen:Nat => OldLen:Nat +Nat Len:Nat), M:Map) ...</ mem >
		[structural] 
		
	op bindVariadic : K List{KResult} -> K 
	op bindVariadic-pre : K List{K} -> K 
	--- the idea here is that there should have been a previous argument, so we can use its address to append all of the variadic arguments
	op promoteList : List{C} -> List{K} 
	ceq promoteList((tv(V:List{K}, T:Type) :: L:List{C})) = (promote(tv(V:List{K}, T:Type)),, promoteList(L:List{C}))
		if ((rank(T:Type) <Int rank(int) orBool hasBitfieldType(T:Type)) andBool hasIntegerType(T:Type)) 
		orBool T:Type ==Bool float 
	ceq promoteList((tv(V:List{K}, T:Type) :: L:List{C})) = (tv(V:List{K}, T:Type),, promoteList(L:List{C}))
		if (notBool(hasIntegerType(T:Type)) orBool rank(T:Type) >=Int rank(int))
		orBool T:Type ==Bool double orBool T:Type ==Bool long-double 

	eq promoteList(Nil) = .List{K} 
	--- fixme report bug: this context doesn't work
	--- op bindVariadic : Nat List{K} -> K 
	
	rule [bind-variadic-start]:
		< k > bind-aux(Loc:Nat, L:List{C}, variadic)
			=> bindVariadic-pre(Loc:Nat, promoteList(L:List{C}))
		...</ k >
		[structural] 
		
	rule [bind-variadic-start]:
		< k > bindVariadic-pre(Loc:Nat, L:List{KResult}) => bindVariadic(Loc:Nat, L:List{KResult}) ...</ k > 
		[structural] 
	
	rule [bind-variadic]:
		< k > (. => bitSizeofType(type(V:Value))) ~> bindVariadic(?, (V:Value,, ?:List{KResult})) ...</ k > 
		[structural] 
	
	rule [bind-variadic-done]:
		< k > bindVariadic(?, .List{K}) => sequencePoint ...</ k > 
		[structural] 

	rule [bind-variadic-withSize]:
		< k > (tv(Len:Nat, ?) => append(Loc:Nat, Len:Nat /Nat numBitsPerByte, V:Value)) 
			~> bindVariadic(Loc:Nat, ((V:Value => .List{K}),, L:List{KResult}))
		...</ k > 
		[structural] 
endkm

kmod COMMON-SEMANTICS-DECLARATIONS-GENERAL is
	including COMMON-SEMANTICS-DECLARATIONS-INCLUDE 

	--- c99 6.7.8:9 Except where explicitly stated otherwise, for the purposes of this subclause unnamed members of objects of structure and union type do not participate in initialization.  Unnamed members of structure objects have indeterminate value even after initialization
	--- c99 6.7.8:10 If an object that has automatic storage duration is not initialized explicitly, its value is indeterminate. If an object that has static storage duration is not initialized explicitly, then:
	--- — if it has pointer type, it is initialized to a null pointer;
	--- — if it has arithmetic type, it is initialized to (positive or unsigned) zero;
	--- if it is an aggregate, every member is initialized (recursively) according to these rules;
	--- — if it is a union, the first named member is initialized (recursively) according to these rules

	op defineType : K -> K [metadata "strict"] 
	context DeclarationDefinition(InitNameGroup(`[HOLE`]:K, ?)) 
	context Typedef(NameGroup(`[HOLE`]:K, ?)) 
	
	rule
		< k > LocalDefinition(DefinitionLoc(K:K, Loc:K)) => DefinitionLoc(K:K, Loc:K) ...</ k >
		[structural] 
	
	--- aggregates
	rule
		< k > figureInitializer(X:Id, T:Type, CompoundInit(L:List{C}))
			=> giveType(X:Id, T:Type)
			~> figureInitializer-aux(X:Id, T:Type, startInitializer(T:Type, X:Id, CompoundInit(L:List{C})))
		...</ k >
		if (hasAggregateType(T:Type) orBool hasUnionType(T:Type)) 
		---andBool notBool hasIncompleteType(T:Type)
		[structural] 
	rule
		< k > figureInitializer(X:Id, arrayType(T:Type, Len:Nat), SingleInit(Constant(StringLiteral(S:String)))) 
			=> figureInitializer(X:Id, arrayType(T:Type, Len:Nat), CompoundInit(InitFragment(NextInit, SingleInit(Constant(StringLiteral(S:String))))))
		...</ k >
		if hasCharType(T:Type)
		andBool lengthString(S:String) <=Nat Len:Nat
		[structural] 
	
	rule
		< k > figureInitializer(X:Id, (incompleteArrayType(T:Type) => arrayType(T:Type, lengthString(S:String) +Nat 1)), SingleInit(Constant(StringLiteral(S:String)))) ...</ k >
		if hasCharType(T:Type)
		[structural] 
		
	rule
		< k > figureInitializer(X:Id, incompleteArrayType(T:Type), CompoundInit(InitFragment(NextInit, SingleInit(Constant(StringLiteral(S:String))))))
			=> figureInitializer(X:Id, incompleteArrayType(T:Type), SingleInit(Constant(StringLiteral(S:String))))
		...</ k >
		[structural] 
		
	--- this comes from function declarations.  should probably adjust this
	rule
		< k > figureInitializer(X:Id, T:Type, initializer(K:K))
			=> figureInitializer-aux(X:Id, T:Type, initializer(K:K))
		...</ k >
		[structural] 

	rule
		< k > figureInitializer-aux(X:Id, T:Type, initializer(K:K))
			=> initializerValue(X:Id, T:Type, K:K)
		...</ k >
		if notBool hasIncompleteType(T:Type) --- I'd like to get rid of this cleanly
		[structural] 
	
	--- base types
	rule
		< k > figureInitializer(X:Id, T:Type, SingleInit(K:K))
			=> figureInitializer-aux(X:Id, T:Type, initializer(Computation(X:Id := K:K)))
		...</ k >
		if notBool hasArrayType(T:Type)
		[structural] 
	--- c1x 6.7.8:11
	rule
		< k > figureInitializer(X:Id, T:Type, CompoundInit(InitFragment(NextInit, SingleInit(K:K))))
			=> figureInitializer-aux(X:Id, T:Type, initializer(Computation(X:Id := K:K)))
		...</ k >
		if notBool (hasAggregateType(T:Type) orBool hasUnionType(T:Type))
		[structural] 
		
	eq DeclarationDefinition(InitNameGroup(T:Type, (K:C :: K':C :: L:List{C}))) 
		= DeclarationDefinition(InitNameGroup(T:Type, K:C)) 
		~> DeclarationDefinition(InitNameGroup(T:Type, K':C :: L:List{C})) 
	eq DeclarationDefinition(InitNameGroup(T:Type, InitName(Name:K, Exp:K))) = declare(SingleName(T:Type, Name:K), Exp:K) 
			
	eq Typedef(NameGroup(T:Type, (K:C :: K':C :: L:List{C}))) = Typedef(NameGroup(T:Type, K:C)) ~> Typedef(NameGroup(T:Type, K':C :: L:List{C})) 
	eq Typedef(NameGroup(T:Type, Name:C)) = defineType(SingleName(T:Type, Name:C)) 
		
	op initialize-aux : Id Type K -> K 
		
	--- c1x 6.7.8:21 ... the remainder of the aggregate shall be initialized implicitly the same as objects that have static storage duration
	rule
		< k > initialize(X:Id, T:Type, K:K)
			=> if (F:Id ==Bool File-Scope) then zero(X:Id) else (.) fi 
			~> K:K
			~> sequencePoint
		...</ k >
		< currentFunction > F:Id </ currentFunction >
		[structural] 

	rule
		< k > zero(Name:K) => zeroType(Name:K, unqualifyType(T:Type)) ...</ k >
		< types >... Name:K |-> T:Type ...</ types >
		--- < currentFunction > F:Id </ currentFunction >
		--- < env >... Name:K |-> sym(Block:Nat) +Nat 0 ...</ env >
		--- < mem >... Block:Nat |-> memblock(Len:Nat, (? => .Map[piece(0, numBitsPerByte) / 0 to Len:Nat])) ...</ mem >
		[structural] 
		
	op zeroType : K Type -> K 
	
	rule
		< k > zeroType(Name:K, T:Type) => Computation(Name:K := tv(0, int)) ...</ k >
		if hasIntegerType(T:Type)
		[structural] 
	rule
		< k > zeroType(Name:K, T:Type) => Computation(Name:K := tv(0.0, float)) ...</ k >
		if hasFloatType(T:Type)
		[structural] 
		
	op zeroStruct : K List{C} -> K 
	
	--- c1x 6.7.9:10 If an object that has automatic storage duration is not initialized explicitly, its value is indeterminate. If an object that has static or thread storage duration is not initialized explicitly, then:
	--- — if it has pointer type, it is initialized to a null pointer;
	--- — if it has arithmetic type, it is initialized to (positive or unsigned) zero;
	--- — if it is an aggregate, every member is initialized (recursively) according to these rules, and any padding is initialized to zero bits;
	--- — if it is a union, the first named member is initialized (recursively) according to these rules, and any padding is initialized to zero bits;
	
	rule
		< k > zeroType(Name:K, structType(S:Id)) 
			=> zeroStruct(Name:K, Fields:List{C})
		...</ k >
		< structs >... S:Id |-> Fields:List{C} ...</ structs > 
		[structural] 
		
	rule
		< k > zeroType(Name:K, unionType(S:Id)) 
			=> zeroType(Name:K . F:Id, T:Type)
		...</ k >
		< structs >... S:Id |-> (typedDeclaration(T:Type, F:Id) :: ?) ...</ structs > 
		[structural] 
		
	rule
		< k > zeroStruct(Name:K, (typedDeclaration(T:Type, F:Id) :: L:List{C})) 
			=> zeroType(Name:K . F:Id, T:Type)
			~> zeroStruct(Name:K, L:List{C}) 
		...</ k >
		[structural] 
	rule
		< k > zeroStruct(Name:K, Nil) => .K ...</ k >
		[structural] 
		
	rule
		< k > zeroType(Name:K, T:Type) => Computation(Name:K := tv(NullPointer, T:Type)) ...</ k >
		if hasFunctionType(T:Type) 
		orBool hasPointerType(T:Type)
		[structural] 
		
	rule
		< k > zeroType(Name:K, arrayType(T:Type, sNat(Len:Nat))) 
			=> zeroType(Name:K[Len:Nat], T:Type)
			~> zeroType(Name:K, arrayType(T:Type, Len:Nat)) 
		...</ k >
		[structural] 
	rule
		< k > zeroType(Name:K, arrayType(T:Type, 0)) => .K ...</ k >
		[structural] 

	rule
		< k > zeroType(Name:K, flexibleArrayType(T:Type))
			=> .K
		...</ k >
		[structural] 
		
	rule
		< k > zeroBlock(sym(Block:Nat) +Nat 0) => . ...</ k >
		< mem >... Block:Nat |-> memblock(Len:Nat, (? => .Map[piece(0, numBitsPerByte) / 0 to Len:Nat])) ...</ mem >
		[structural] 
	
	rule
		< k > defineType(typedDeclaration(T:Type, X:Id)) => giveType(typedef(X:Id), T:Type) ...</ k >
		[structural] 
			
	op declareFunction : Id Type K -> K 
	op declareExternalVariable : Id Type K -> K 
	op declareInternalVariable : Id Type K -> K 
	
	--- function definition
	rule
		< k > declare(typedDeclaration(T:Type, X:Id), K:K) 
			=> declareFunction(X:Id, T:Type, K:K)
		...</ k >
		< currentFunction > File-Scope </ currentFunction >
		if notBool hasIncompleteType(T:Type) --- I'd like to get rid of this cleanly
		andBool hasFunctionType(T:Type)
		[structural] 
		
	--- fixme there are still no nested functions though, right?
	rule
		< k > declare(typedDeclaration(T:Type, X:Id), NoInit) 
			=> addToEnv(X:Id, Loc:Nat)
			~> giveType(X:Id, unqualifyType(T:Type))
		...</ k >
		< externalLocations >... X:Id |-> Loc:Nat ...</ externalLocations > 
		< currentFunction > F:K </ currentFunction >
		if notBool hasIncompleteType(T:Type) --- I'd like to get rid of this cleanly
		andBool hasFunctionType(T:Type)
		andBool F:K =/=Bool File-Scope
		[structural] 
	rule
		< k > declare(typedDeclaration(T:Type, X:Id), K:K)
			=> declareExternalVariable(X:Id, T:Type, K:K)
		...</ k >
		< currentFunction > File-Scope </ currentFunction >
		--- if notBool hasIncompleteType(T:Type) --- I'd like to get rid of this cleanly
		if notBool hasFunctionType(T:Type)
		[structural] 
	rule
		< k > declare(typedDeclaration(T:Type, X:Id), K:K) 
			=> declareInternalVariable(X:Id, T:Type, K:K)
		...</ k >
		< currentFunction > F:K </ currentFunction >
		--- if notBool hasIncompleteType(T:Type) --- I'd like to get rid of this cleanly
		if notBool hasFunctionType(T:Type)
		andBool F:K =/=Bool File-Scope
		[structural] 
		
	---- external variables
	--- feature request : nice to have MapList
	
	--- function definition
	rule
		< k > declareFunction(X:Id, T:Type, K:K)
			=> declareWithLinkage(X:Id, T:Type, K:K, external)
		...</ k >
		if notBool hasStaticType(T:Type)
		andBool K:K =/=Bool NoInit
		[structural] 

	rule
		< k > declareFunction(X:Id, T:Type, NoInit)
			=> declareWithLinkage(X:Id, prototype(T:Type), NoInit, external)
		...</ k >
		if notBool hasStaticType(T:Type)
		[structural] 
		
	--- fixme not handling internal prototypes
	rule
		< k > declareFunction(X:Id, T:Type, K:K)
			=> declareWithLinkage(X:Id, T:Type, K:K, internal)
		...</ k >
		< currentFunction > File-Scope </ currentFunction >
		if hasStaticType(T:Type)
		[structural] 
		
		
	
	op declareWithLinkage : Id Type K K -> K --- id, type, possible init, linkage (external, internal, noLinkage)
	
	---- internal variables
	
	--- fixme need to look for bad use
	rule
		< k > declareInternalVariable(X:Id, T:Type, K:K)
			=> declareWithLinkage(X:Id, T:Type, K:K, noLinkage)
		...</ k >
		if notBool hasStaticType(T:Type)
		andBool notBool hasExternType(T:Type)
		[structural] 
		
	rule
		< k > declareInternalVariable(X:Id, T:Type, NoInit)
			=> addToEnv(X:Id, Loc:Nat)
			~> giveType(X:Id, unqualifyType(T:Type))
		...</ k >
		< internalLocations >... Tu:K |-> Map((? kpair(X:Id, BlockNum:Nat) |-> Loc:Nat)) ...</ internalLocations >
		< blockHistory > ListItem(BlockNum:Nat) ...</ blockHistory >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		if hasStaticType(T:Type)
		andBool notBool hasExternType(T:Type)
		[structural] 
	rule
		< k > declareInternalVariable(X:Id, T:Type, NoInit)
			=> allocateType(Loc:Nat, T:Type)
			~> addToEnv(X:Id, Loc:Nat)
			~> giveType(X:Id, unqualifyType(T:Type))
			~> zero(X:Id)
		...</ k >
		< internalLocations >... Tu:K |-> Map((Locs:Map => Locs:Map[Loc:Nat / kpair(X:Id, BlockNum:Nat)])) ...</ internalLocations >
		< blockHistory > ListItem(BlockNum:Nat) ...</ blockHistory >
		< nextLoc > Loc:Nat => inc(Loc:Nat) </ nextLoc >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		if hasStaticType(T:Type)
		andBool notBool hasExternType(T:Type)
		andBool notBool $hasMapping(Locs:Map, kpair(X:Id, BlockNum:Nat))
		[structural] 
		
	rule
		< k > declareInternalVariable(X:Id, T:Type, K:K)
			=> defineAndInit(X:Id, unqualifyType(T:Type), figureInitializer(X:Id, unqualifyType(T:Type), K:K), Loc:Nat)
		...</ k >
		< internalLocations >... Tu:K |-> Map((Locs:Map => Locs:Map[Loc:Nat / kpair(X:Id, BlockNum:Nat)])) ...</ internalLocations >
		< blockHistory > ListItem(BlockNum:Nat) ...</ blockHistory >
		< nextLoc > Loc:Nat => inc(Loc:Nat) </ nextLoc >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		if hasStaticType(T:Type)
		andBool notBool hasExternType(T:Type)
		andBool K:K =/=Bool NoInit
		andBool notBool $hasMapping(Locs:Map, kpair(X:Id, BlockNum:Nat))
		[structural] 
		
	op restoreShouldInit : Bool -> K 
	rule
		< k > restoreShouldInit(OldShouldValue:Bool) => . ...</ k >
		< shouldInit > ? => OldShouldValue:Bool </ shouldInit >
		[structural] 
		
	--- statics should only be initialized once.  if we've already seen it, we still need to calculate type, but don't init
	--- rule
		--- < k > declareInternalVariable(X:Id, T:Type, K:K)
			--- => defineAndInit(X:Id, unqualifyType(T:Type), figureInitializer(X:Id, unqualifyType(T:Type), K:K), Loc:Nat)
			--- ~> restoreShouldInit(OldShouldValue:Bool)
		--- ...</ k >
		--- < internalLocations >... Tu:K |-> Map((? kpair(X:Id, BlockNum:Nat) |-> Loc:Nat)) ...</ internalLocations >
		--- < blockHistory > ListItem(BlockNum:Nat) ...</ blockHistory >
		--- < currentTranslationUnit > Tu:K </ currentTranslationUnit >
		--- < shouldInit > OldShouldValue:Bool => false </ shouldInit >
		--- if hasStaticType(T:Type)
		--- andBool notBool hasExternType(T:Type)
		--- andBool K:K =/=Bool NoInit
		--- [structural] 
		
	--- this is essentially defineandinit, but that checks if type has been seen for allocation
	op reseenStatic : Id Type K Nat -> K [metadata "strict(3)"] 
	rule
		< k > declareInternalVariable(X:Id, T:Type, K:K)
			=> reseenStatic(X:Id, unqualifyType(T:Type), figureInitializer(X:Id, unqualifyType(T:Type), K:K), Loc:Nat)
		...</ k >
		< internalLocations >... Tu:K |-> Map((? kpair(X:Id, BlockNum:Nat) |-> Loc:Nat)) ...</ internalLocations >
		< blockHistory > ListItem(BlockNum:Nat) ...</ blockHistory >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		if hasStaticType(T:Type)
		andBool notBool hasExternType(T:Type)
		andBool K:K =/=Bool NoInit
		[structural] 
		
	rule
		< k > reseenStatic(X:Id, ?, initializerValue(X:Id, T:Type, ?), Loc:Nat)
			=> addToEnv(X:Id, Loc:Nat)
			~> giveType(X:Id, T:Type)
		...</ k >
		[structural] 
		
		
	rule
		< k > declareInternalVariable(X:Id, T:Type, NoInit)
			=> addToEnv(X:Id, Loc:Nat)
			~> giveType(X:Id, unqualifyType(T:Type))
		...</ k >
		< externalLocations >... X:Id |-> Loc:Nat ...</ externalLocations >
		if notBool hasIncompleteType(T:Type)
		andBool notBool hasStaticType(T:Type)
		andBool hasExternType(T:Type)
		[structural] 
		
	
	---- external variables
	rule
		< k > declareExternalVariable(X:Id, T:Type, K:K)
			=> declareWithLinkage(X:Id, T:Type, K:K, external)
		...</ k >
		if notBool hasStaticType(T:Type)
		andBool notBool hasExternType(T:Type)
		[structural] 
	rule
		< k > declareExternalVariable(X:Id, T:Type, K:K)
			=> declareWithLinkage(X:Id, T:Type, K:K, external)
		...</ k >
		< preLinkage >... Tu:K |-> Map(Linkage:Map) ...</ preLinkage >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		if notBool hasStaticType(T:Type)
		andBool hasExternType(T:Type)
		andBool notBool $hasMapping(Linkage:Map, X:Id)
		[structural] 
	rule
		< k > declareExternalVariable(X:Id, T:Type, K:K)
			=> declareWithLinkage(X:Id, T:Type, K:K, Linkage:Map(X:Id))
		...</ k >
		< preLinkage >... Tu:K |-> Map(Linkage:Map) ...</ preLinkage >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		if notBool hasStaticType(T:Type)
		andBool hasExternType(T:Type)
		andBool $hasMapping(Linkage:Map, X:Id)
		[structural] 
	rule
		< k > declareExternalVariable(X:Id, T:Type, K:K)
			=> declareWithLinkage(X:Id, T:Type, K:K, internal)
		...</ k >
		if hasStaticType(T:Type)
		andBool notBool hasExternType(T:Type)
		[structural] 
		
	op declareOnly : Id Type K -> K 
	op declareAndDefine : Id Type K K -> K 

	rule
		< k > declareWithLinkage(X:Id, T:Type, NoInit, L:K) => declareOnly(X:Id, T:Type, L:K) ...</ k >
		< declarationOrder >... Tu:K |-> ListToK(? (. => ListItem(X:Id))) ...</ declarationOrder >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		if L:K =/=Bool noLinkage
		[structural] 
	rule
		< k > declareWithLinkage(X:Id, T:Type, K:K, L:K) => declareAndDefine(X:Id, T:Type, K:K, L:K) ...</ k >
		< declarationOrder >... Tu:K |-> ListToK(? (. => ListItem(X:Id))) ...</ declarationOrder >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		if K:K =/=Bool NoInit
		andBool L:K =/=Bool noLinkage
		[structural] 
		
	--- fixme this terribly needs to be refactored.  I'm duplicating the above two rules so I don't add locals to the declaration order
	rule
		< k > declareWithLinkage(X:Id, T:Type, NoInit, L:K) => declareOnly(X:Id, T:Type, L:K) ...</ k >
		--- < declarationOrder >... Tu:K |-> ListToK(? (. => ListItem(X:Id))) ...</ declarationOrder >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		if L:K ==Bool noLinkage
		[structural] 
	rule
		< k > declareWithLinkage(X:Id, T:Type, K:K, L:K) => declareAndDefine(X:Id, T:Type, K:K, L:K) ...</ k >
		--- < declarationOrder >... Tu:K |-> ListToK(? (. => ListItem(X:Id))) ...</ declarationOrder >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		if K:K =/=Bool NoInit
		andBool L:K ==Bool noLinkage
		[structural] 
	
	--- extern functions are no different than functions
	--- fixme dangerous if someone marks it as static and extern.  can't tell
	ceq qualifiedType(T:Type, Extern) = T:Type
		if hasFunctionType(T:Type) 
	
	--- fixme clean these up, they are so redundant
	--- fixme unqualifying these is probably unsafe
	rule
		< k > declareOnly(X:Id, T:Type, external)
			=> .K
		...</ k >
		< declarations >... (.).Set => SetItem(X:Id) ...</ declarations >
		< preLinkage >... Tu:K |-> Map((Linkage:Map => Linkage:Map[external / X:Id])) ...</ preLinkage >
		< preTypes >... Tu:K |-> Map((Types:Map => Types:Map[T:Type / X:Id])) ...</ preTypes >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		if (notBool $hasMapping(Linkage:Map, X:Id) 
				orBool Linkage:Map(X:Id) ==Bool external
			)
			andBool (
				notBool $hasMapping(Types:Map, X:Id)
				--- orBool Types:Map(X:Id) ==Bool prototype(T:Type)
				orBool isTypeCompatible(unqualifyType(Types:Map(X:Id)), unqualifyType(T:Type))
			)
		[structural] 
		
	rule
		< k > declareOnly(X:Id, prototype(T:Type), external)
			=> .K
		...</ k >
		< preLinkage >... Tu:K |-> Map((Linkage:Map => Linkage:Map[external / X:Id])) ...</ preLinkage >
		< preTypes >... Tu:K |-> Map(Types:Map) ...</ preTypes >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		if (notBool $hasMapping(Linkage:Map, X:Id) 
				orBool Linkage:Map(X:Id) ==Bool external
			)
			andBool isTypeCompatible(unqualifyType(Types:Map(X:Id)), unqualifyType(T:Type))
		[structural]
	
	--- fixme haven't thought about this much, is it right?
	rule
		< k > declareOnly(X:Id, T:Type, internal)
			=> .K
		...</ k >
		< declarations >... (.).Set => SetItem(X:Id) ...</ declarations >
		< preLinkage >... Tu:K |-> Map((Linkage:Map => Linkage:Map[internal / X:Id])) ...</ preLinkage >
		< preTypes >... Tu:K |-> Map((Types:Map => Types:Map[T:Type / X:Id])) ...</ preTypes >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		if notBool $hasMapping(Linkage:Map, X:Id) 
		orBool Linkage:Map(X:Id) ==Bool internal
		[structural] 
	rule
		< k > declareOnly(X:Id, T:Type, noLinkage)
			=> allocateType(Loc:Nat, T:Type)
			~> addToEnv(X:Id, Loc:Nat)
			~> giveType(X:Id, T:Type)
		...</ k >
		< nextLoc > Loc:Nat => inc(Loc:Nat) </ nextLoc >
		< localVariables > Vars:List (. => ListItem(X:Id)) </ localVariables >
		< localAddresses >... (.).Set => SetItem(Loc:Nat) ...</ localAddresses >
		if notBool hasIncompleteType(T:Type)
		andBool notBool hasStaticType(T:Type)
		andBool notBool hasExternType(T:Type)
		andBool notBool X:Id in Vars:List
		[structural] 
	
	--- exception to multiple definitions for functions since we consider prototypes to be definitions to some extent
	rule
		< k > declareAndDefine(X:Id, T:Type, K:K, external)
			=> .K
		...</ k >
		< declarations >... (.).Set => SetItem(X:Id) ...</ declarations >
		--- < externalDefinitions > Def:Map => Def:Map[declarationObject(unqualifyType(T:Type), Tu:K, K:K) / X:Id] </ externalDefinitions >
		< externalDefinitions > Def:Map => Def:Map (X:Id |-> declarationObject(unqualifyType(T:Type), Tu:K, K:K)) </ externalDefinitions >
		< preLinkage >... Tu:K |-> Map((Linkage:Map => Linkage:Map[external / X:Id])) ...</ preLinkage >
		< preTypes >... Tu:K |-> Map((Types:Map => Types:Map[T:Type / X:Id])) ...</ preTypes >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		if (notBool $hasMapping(Def:Map, X:Id) orBool hasFunctionType(T:Type))
		andBool (notBool $hasMapping(Linkage:Map, X:Id) orBool Linkage:Map(X:Id) ==Bool external)
		[structural] 
		
	rule
		< k > declareAndDefine(X:Id, T:Type, K:K, internal)
			=> .K
		...</ k >
		< declarations >... (.).Set => SetItem(X:Id) ...</ declarations >
		< internalDefinitions >... Tu:K |-> Map((Def:Map => Def:Map[declarationObject(unqualifyType(T:Type), Tu:K, K:K) / X:Id])) ...</ internalDefinitions >
		< preLinkage >... Tu:K |-> Map((Linkage:Map => Linkage:Map[internal / X:Id])) ...</ preLinkage >
		< preTypes >... Tu:K |-> Map((Types:Map => Types:Map[T:Type / X:Id])) ...</ preTypes >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		if notBool $hasMapping(Def:Map, X:Id)
		andBool (notBool $hasMapping(Linkage:Map, X:Id) orBool Linkage:Map(X:Id) ==Bool internal)
		[structural] 
	op defineAndInit : Id Type K Nat -> K [metadata "strict(3)"] 
	rule
		< k > declareAndDefine(X:Id, T:Type, K:K, noLinkage)
			=> defineAndInit(X:Id, T:Type, figureInitializer(X:Id, T:Type, K:K), Loc:Nat)
		...</ k >
		< nextLoc > Loc:Nat => inc(Loc:Nat) </ nextLoc >
		< localVariables > Vars:List (. => ListItem(X:Id)) </ localVariables >
		< localAddresses >... (.).Set => SetItem(Loc:Nat) ...</ localAddresses >
		if notBool X:Id in Vars:List
		[structural] 
		
	rule
		< k > defineAndInit(X:Id, ?, initializerValue(X:Id, T:Type, K:K), Loc:Nat)
			=> allocateTypeIfAbsent(Loc:Nat, T:Type)
			~> addToEnv(X:Id, Loc:Nat)
			~> giveType(X:Id, T:Type)
			~> initialize(X:Id, T:Type, K:K)
		...</ k >
		< shouldInit > true </ shouldInit >
		[structural] 
		
	rule
		< k > defineAndInit(X:Id, ?, initializerValue(X:Id, T:Type, ?), Loc:Nat)
			=> allocateTypeIfAbsent(Loc:Nat, T:Type)
			~> addToEnv(X:Id, Loc:Nat)
			~> giveType(X:Id, T:Type)
			--- ~> initialize(X:Id, T:Type, K:K)
		...</ k >
		< shouldInit > false </ shouldInit >
		[structural]
		
	rule
		< k > figureInitializer-aux(?, (incompleteArrayType(T:Type) => arrayType(T:Type, N:Nat)), initializer(K:K))
		...</ k >
		< incompleteLength > N:Nat </ incompleteLength >
		[structural] 

	op allocateAndZeroIfAbsent : Type Id -> K 
	op addToLinkage : Id Type -> K 
	op addToGlobalEnv : K Nat -> K 
	op addToLocalEnv : K Nat -> K 
	
	rule
		< k > addToEnv(X:Id, Loc:Nat) => addToGlobalEnv(X:Id, Loc:Nat) ...</ k >
		< currentFunction > File-Scope </ currentFunction >
		[structural] 
	rule
		< k > addToEnv(X:Id, Loc:Nat) => addToLocalEnv(X:Id, Loc:Nat) ...</ k >
		< currentFunction > F:K </ currentFunction >
		if F:K =/=Bool File-Scope
		[structural] 
		
	rule
		< k > addToGlobalEnv(X:Id, Loc:Nat) => . ...</ k >
		< genv >... Tu:K |-> Map((M':Map => M':Map[Loc:Nat / X:Id])) ...</ genv >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		< env > E:Map => E:Map[Loc:Nat / X:Id] </ env >
		[structural] 
	rule
		< k > addToLocalEnv(X:Id, Loc:Nat) => . ...</ k >
		< env > E:Map => E:Map[Loc:Nat / X:Id] </ env >
		[structural] 
			
	rule
		< k > DeclarationDefinition(InitNameGroup(T:Type, Nil)) => .K ...</ k >
		[structural] 
	
	op defineUsingOldDeclaration : Type Id K -> K 
	
	--- op defineFunctionUsingOldDeclaration : Type Id K -> K 
	--- FIXME check prototypes
	rule [function-definition]:
		< k > FunctionDefinition(typedDeclaration(T:Type, X:Id), Block:K) 
			=> declareFunction(X:Id, T:Type, initializer(Computation(X:Id := tv(functionObject(X:Id, unqualifyType(T:Type), Block:K), T:Type))))
			~> calculateGotoMap(X:Id, Block:K)
		...</ k >
		if hasFunctionType(T:Type)
		[structural] 
endkm

kmod COMMON-SEMANTICS-DECLARATIONS-INITIALIZATIONS is
	including COMMON-SEMANTICS-DECLARATIONS-INCLUDE 
	
	op te : K Type -> K 
	op getInitializer : -> K 
	op fillInitializer : K -> K 
	op fillInitializer-aux : K -> K 
	op fillInitializer : List{C} -> K 
	op completeInitializerFragment : K K -> C 
	op initializerFragment : K -> KResult 
	
	rule
		< k > getInitializer => initializer(K:C) ...</ k >
		< savedInitialization > K:C => . </ savedInitialization > 
		< currentObject > ?:List => . </ currentObject > 
		< currentSubObject > ?:List => . </ currentSubObject > 
		[structural] 

	rule
		< k > startInitializer(T:Type, X:Id, CompoundInit(L:List{C}))
			=> fillInitializer(L:List{C}) ~> getInitializer
		...</ k >
		< incompleteLength > ? => 0 </ incompleteLength >
		< currentSubObject > . => ListItem(te(X:Id, T:Type)) </ currentSubObject >
		< currentObject > . => ListItem(te(X:Id, T:Type)) </ currentObject >
		< savedInitialization >... . => zero(X:Id) </ savedInitialization > 
		if hasUnionType(T:Type) orBool hasAggregateType(T:Type)
		[structural] 
	
	rule
		< k > fillInitializer(InitFragment(K:K, Exp:K) :: L:List{C})
		=> fillInitializer(InitFragment(K:K, Exp:K)) ~> fillInitializer(L:List{C})
		...</ k >
		[structural] 
	rule
		< k > fillInitializer(Nil) => . ...</ k >
		[structural] 
	
	op next : -> ListItem 
	op block : -> ListItem 
	
	rule
		< currentSubObject > 
			ListItem(te(K:K, arrayType(T:Type, Len:Nat)))
			=> ListItem(te(K:K[0], T:Type)) ListItem(te(K:K, arrayType(T:Type, Len:Nat)))
		...</ currentSubObject >
		[structural] 
	rule
		< currentSubObject > 
			ListItem(te(K:K, incompleteArrayType(T:Type)))
			=> ListItem(te(K:K[0], T:Type)) ListItem(te(K:K, incompleteArrayType(T:Type)))
		...</ currentSubObject >
		[structural] 
	rule
		< currentSubObject > 
			ListItem(te(K:K, structType(S:Id)))
			=> ListItem(te(K:K . F:Id, T:Type)) ListItem(te(K:K, structType(S:Id)))
		...</ currentSubObject >
		< structs >... S:Id |-> typedDeclaration(T:Type, F:Id) :: ? ...</ structs > 
		[structural] 
	rule
		< currentSubObject > 
			ListItem(te(K:K, unionType(S:Id)))
			=> ListItem(te(K:K . F:Id, T:Type)) ListItem(te(K:K, unionType(S:Id)))
		...</ currentSubObject >
		< structs >... S:Id |-> typedDeclaration(T:Type, F:Id) :: ? ...</ structs > 
		[structural] 
		
	--- fixme should i worry about basetype here?
	rule [init-next-array-element]:
		< currentSubObject > 
			(next ListItem(te(K:K[N:Nat], T:Type)) => ListItem(te(K:K[sNat(N:Nat)], T:Type)))
			ListItem(te(K:K, arrayType(?, Len:Nat)))
		...</ currentSubObject >
		if Len:Nat >Nat sNat(N:Nat)
		[structural] 
	rule [init-next-array-element-done]:
		< currentSubObject >
			next (ListItem(te(K:K[N:Nat], T:Type)) => .) ListItem(te(K:K, arrayType(?, Len:Nat)))
		...</ currentSubObject >
		if notBool Len:Nat >Nat sNat(N:Nat)
		[structural] 
	
	rule [init-next-incomplete-array-element]:
		< currentSubObject >
			(next ListItem(te(K:K[N:Nat], T:Type)) => ListItem(te(K:K[sNat(N:Nat)], T:Type))) 
			ListItem(te(K:K, incompleteArrayType(?)))
		...</ currentSubObject >
		---< incompleteLength > N':Nat => maxNat(sNat(N:Nat), N':Nat) </ incompleteLength >
		[structural] 
	
	rule [init-next-struct-element]:
		< currentSubObject >
			next ListItem(te(K:K . F:Id, T:Type)) ListItem(te(K:K, structType(S:Id)))
			=> ListItem(te(K:K . F':Id, T':Type)) ListItem(te(K:K, structType(S:Id)))
		...</ currentSubObject >
		< structs >...
			S:Id |-> ? :: typedDeclaration(T:Type, F:Id) :: typedDeclaration(T':Type, F':Id) :: ? 
		...</ structs > 
		if F':Id =/=Bool #NoName
		[structural] 
	 
	rule [init-next-struct-element]:
		< currentSubObject >
			next ListItem(te(K:K . F:Id, T:Type)) ListItem(te(K:K, structType(S:Id)))
			=> ListItem(te(K:K . F':Id, T':Type)) ListItem(te(K:K, structType(S:Id)))
		...</ currentSubObject >
		< structs >...
			S:Id |-> ? :: typedDeclaration(T:Type, F:Id) :: typedDeclaration(?, #NoName) :: typedDeclaration(T':Type, F':Id) :: ? 
		...</ structs >
		[structural] 
		
	rule [init-next-struct-element-done]:
		< currentSubObject >
			next (ListItem(te(K:K . F:Id, T:Type)) => .) ListItem(te(K:K, structType(S:Id)))
		...</ currentSubObject >
		< structs >...
			S:Id |-> ? :: typedDeclaration(T:Type, F:Id)
		...</ structs > 
		[structural] 
	rule [init-next-struct-element-done]:
		< currentSubObject >
			next (ListItem(te(K:K . F:Id, T:Type)) => .) ListItem(te(K:K, structType(S:Id)))
		...</ currentSubObject >
		< structs >...
			S:Id |-> ? :: typedDeclaration(T:Type, F:Id) :: typedDeclaration(?, #NoName)
		...</ structs > 
		[structural] 
		
	rule [init-next-union-element-done]:
		< currentSubObject >
			next (ListItem(te(K:K . ?, T:Type)) => .) ListItem(te(K:K, unionType(S:Id)))
		...</ currentSubObject >
		[structural] 
		
	rule
		< k > fillInitializer(InitFragment(NextInit, Exp:K)) => fillInitializer(Exp:K) ...</ k >
		[structural] 
		
	op finishCompoundInit : List -> K 
	rule
		< k > fillInitializer(CompoundInit(L:List{C})) 
			=> fillInitializer(L:List{C})
			--- ~> debug
			~> finishCompoundInit(next ListItem(te(K:K, T:Type)) Remainder:ListItem)
		...</ k >
		< currentSubObject > (?:List => .) ListItem(te(K:K, T:Type)) (Remainder:ListItem => .) </ currentSubObject >
		< currentObject > (. => ListItem(te(K:K, T:Type))) ...</ currentObject >
		if hasAggregateType(T:Type) orBool hasUnionType(T:Type)
		[metadata "computational"] --- fixme computational to make sure all the other equations have applied first
	rule
		< k > finishCompoundInit(L:List) => 
			. 
			--- debug
		...</ k >
		< currentObject > (ListItem(te(K:K, T:Type)) => .) ...</ currentObject >
		< currentSubObject > (? => L:List) </ currentSubObject >
		[structural] 
			
	context fillInitializer(InitFragment(`[HOLE`]:K, ?)) 
	op buildDesignator : K -> K 
	
	--- note that these clear the current subobject cell, because it will be repopulated when building the designator
	rule
		< k > fillInitializer(InitFragment(InFieldInit(F:Id, K':K), Exp:K))
			=> fillInitializer(InitFragment(buildDesignator(InFieldInit(F:Id, K':K)), Exp:K))
		...</ k >
		< currentObject > ListItem(te(K:K, T:Type)) ...</ currentObject >
		< currentSubObject > ?:List => block ListItem(te(K:K, T:Type)) </ currentSubObject >
		if hasStructType(T:Type) orBool hasUnionType(T:Type)
		[structural] 
	--- fixme does this need to worry about incompleteLength?
	rule
		< k > fillInitializer(InitFragment(AtIndexInit(Index:K, K':K), Exp:K))
			=> fillInitializer(InitFragment(buildDesignator(AtIndexInit(Index:K, K':K)), Exp:K))
		...</ k >
		< currentObject > ListItem(te(K:K, T:Type)) ...</ currentObject >
		< currentSubObject > ?:List => block ListItem(te(K:K, T:Type)) </ currentSubObject >
		if hasArrayType(T:Type)
		[structural] 
		
	
	--- fixme these are also too restrictive on type.  if we try to assign an int to a long-int field, it will fail
	--- i don't think this is true anymore
	rule
		< k > buildDesignator(InFieldInit(F:Id, More:K)) 
			=> buildDesignator(More:K)
		...</ k >
		< currentSubObject > block (. => ListItem(te(K:K . F:Id, T:Type))) ListItem('te(K:K,, KL:KLabel(S:Id))) ...</ currentSubObject >
		< structs >... S:Id |-> ? :: typedDeclaration(T:Type, F:Id) :: ? ...</ structs >
		if KL:KLabel ==Bool 'structType 
		orBool KL:KLabel ==Bool 'unionType
		[structural] 
		
	rule
		< k > buildDesignator(NextInit) => NextInit ...</ k >
		< currentSubObject > (block => .) ...</ currentSubObject >
		[structural] 
		
	eq innerType(arrayType(T:Type, ?)) = T:Type 
	eq innerType(incompleteArrayType(T:Type)) = T:Type 
	eq innerType(qualifiedType(T:Type, ?)) = innerType(T:Type) 

	context buildDesignator(AtIndexInit(`[HOLE`]:K, ?)) 
	rule
		< k > buildDesignator(AtIndexInit(tv(N:Nat, ?), More:K)) 
			=> buildDesignator(More:K)
		...</ k >
		< currentSubObject > block (. => ListItem(te(K:K[N:Nat], innerType(T:Type)))) ListItem(te(K:K, T:Type)) ...</ currentSubObject >
		if hasArrayType(T:Type)
		[structural] 
	
	op popInit : -> K
	
	op getTopArrayUse : K -> Nat 
	eq getTopArrayUse(X:Id) = 0 
	eq getTopArrayUse(X:Id[N:Nat]) = sNat(N:Nat) --- +1 for length instead of index
	eq getTopArrayUse(K:K . F:Id) = getTopArrayUse(K:K) 
	eq getTopArrayUse((K:K[N:Nat])[?]) = getTopArrayUse(K:K[N:Nat]) 
	eq getTopArrayUse((K:K . F:Id)[?]) = getTopArrayUse(K:K) 
	
	op initializeSingleInit : K -> K 
		
	rule
		< k > (. => typeof(K:K)) ~> initializeSingleInit(K:K) ...</ k >
		[structural] 
	
	--- fixme want to exclude strings, but not normal arrays
	rule
		< k > T':Type ~> initializeSingleInit(K':K) => . ...</ k >
		< currentSubObject > (. => next) ListItem(te(K:K, T:Type)) ...</ currentSubObject >
		< incompleteLength > N:Nat => maxNat(N:Nat, getTopArrayUse(K:K)) </ incompleteLength >
		< savedInitialization >... . => Computation(K:K := K':K) </ savedInitialization > 
		if (isABaseType(T:Type) orBool hasPointerType(T:Type) orBool hasBitfieldType(T:Type))
		andBool notBool hasStructType(T':Type)
		andBool notBool hasUnionType(T':Type)
		[structural] 
		
	--- this is used to have an aggregate on the RHS of a compound init
	--- fixme want to exclude strings, but not normal arrays
	op initFromAggregateRHS : K Type -> K 
	rule
		< k > T:Type ~> initializeSingleInit(K:K) => initFromAggregateRHS(K:K, T:Type) ...</ k >
		--- if hasAggregateType(T:Type) 		
		if hasStructType(T:Type)
		orBool hasUnionType(T:Type)
		[structural] 
		
	op initFromStructRHS : K Type List{C} -> K 
	rule
		< k > initFromAggregateRHS(K:K, structType(S:Id)) 
			=> initFromStructRHS(K:K, structType(S:Id), L:List{Type}) 
		...</ k >
		< currentSubObject > . => findStruct(structType(S:Id)) ...</ currentSubObject >
		< structs >...
			S:Id |-> L:List{Type}
		...</ structs >
		[structural] 
		
	op findStruct : Type -> ListItem 
		
	rule
		< currentSubObject > findStruct(T:Type) (ListItem(te(?, T':Type)) => .) ...</ currentSubObject >
		if T:Type =/=Bool T':Type
		[structural] 
		
	--- fixme unsafe, might have started to initialize other things
	rule
		< k > initFromStructRHS(K':K, structType(S:Id), ?)
			=> .K
		...</ k >
		< currentSubObject > findStruct(structType(S:Id)) ListItem(te(K:K, structType(S:Id))) => next ...</ currentSubObject >
		< incompleteLength > N:Nat => maxNat(N:Nat, getTopArrayUse(K:K)) </ incompleteLength >
		< savedInitialization >... . => Computation(K:K := K':K) </ savedInitialization > 
		[structural] 
	
	rule
		< k > fillInitializer(SingleInit(K:K)) => initializeSingleInit(K:K) ...</ k >
		if getKLabel(K:K) =/=Bool 'Constant
		[structural] 
	rule
		< k > fillInitializer(SingleInit(Constant(K:K))) => initializeSingleInit(Constant(K:K)) ...</ k >
		if getKLabel(K:K) =/=Bool 'StringLiteral
		andBool getKLabel(K:K) =/=Bool 'WStringLiteral
		[structural] 

	rule
		< k > fillInitializer(SingleInit(Constant(StringLiteral(S:String))))
			=> fillInitializer-aux(SingleInit(Constant(StringLiteral(S:String))))
		...</ k >
		< currentSubObject > ListItem(te(K:K, T:Type)) ListItem(te(?, arrayType(T:Type, Len:Nat))) ...</ currentSubObject >
		if hasCharType(T:Type)
		andBool lengthString(S:String) ==Bool Len:Nat
		[structural] 
	rule
		< k > fillInitializer(SingleInit(Constant(StringLiteral(S:String))))
			=> fillInitializer(SingleInit(Constant(StringLiteral(S:String +String "\0"))))
		...</ k >
		< currentSubObject > ListItem(te(K:K, T:Type)) ListItem(te(?, arrayType(T:Type, Len:Nat))) ...</ currentSubObject >
		if hasCharType(T:Type)
		andBool lengthString(S:String) <Int Len:Nat
		[structural] 
	rule
		< k > fillInitializer(SingleInit(Constant(StringLiteral(S:String))))
			=> fillInitializer-aux(SingleInit(Constant(StringLiteral(S:String +String "\0"))))
		...</ k >
		< currentSubObject > ListItem(te(K:K, T:Type)) ListItem(te(?, incompleteArrayType(T:Type))) ...</ currentSubObject >
		if hasCharType(T:Type)
		[structural] 
		
	rule
		< k > fillInitializer-aux(SingleInit(Constant(StringLiteral(S:String))))
			=> fillInitializer(SingleInit(tv(charToAscii(firstChar(S:String)), char))) 
			~> fillInitializer-aux(SingleInit(Constant(StringLiteral(butFirstChar(S:String))))) 
		...</ k >
		< currentSubObject > ListItem(te(K:K, T:Type)) ...</ currentSubObject >
		if S:String =/=Bool ""
		andBool hasCharType(T:Type)
		[structural] 
	--- fixme not sure what happens in the case of   char *x = "";
	rule
		< k > fillInitializer-aux(SingleInit(Constant(StringLiteral("")))) => . ...</ k >
		--- if hasCharType(T:Type)
		[structural] 
		
	--- this rule assumes all unrollings have already occurred, so it needs to be a rule
	--- alternatively, i've added the condition below which might be enough
	rule
		< k > fillInitializer(SingleInit(Constant(StringLiteral(S:String))))
			=> initializeSingleInit(Constant(StringLiteral(S:String)))
		...</ k >
		< currentSubObject > ListItem(te(K:K, T:Type)) ...</ currentSubObject >
		if notBool hasCharType(T:Type)
		andBool (isABaseType(T:Type) orBool hasPointerType(T:Type) orBool hasBitfieldType(T:Type))
		[structural] 
endkm


kmod COMMON-SEMANTICS-DECLARATIONS-RESOLUTION is
	including COMMON-SEMANTICS-DECLARATIONS-INCLUDE 
	
	op canonicalizeTranslationUnitVariables : -> K 
	rule
		< k > TranslationUnit(Name:String, L:List{C}, P:String) 
			=> listToK(L:List{C})
		...</ k >
		< currentTranslationUnit > ? => Name:String </ currentTranslationUnit >
		< declarationOrder > DeclOrder:Map => DeclOrder:Map[ListToK((.).List) / Name:String] </ declarationOrder >
		< internalLocations > ExtLoc:Map => ExtLoc:Map[Map(.) / Name:String] </ internalLocations >
		< functionTranslationUnits > Funs:Map => Funs:Map[Map(.) / Name:String] </ functionTranslationUnits > 
		< translationUnits >... . => BagItem(Name:String) ...</ translationUnits >
		< preLinkage > Linkage:Map => Linkage:Map[Map(.) / Name:String] </ preLinkage >
		< preTypes > Types:Map => Types:Map[Map(.) / Name:String] </ preTypes >
		< internalDefinitions > Def:Map => Def:Map[Map(.) / Name:String] </ internalDefinitions >
		< genv > Env:Map => Env:Map[Map(.) / Name:String] </ genv >
		< gtypes > Gtypes:Map => Gtypes:Map[Map(.) / Name:String]</ gtypes >
		< programText > M:Map => M:Map[P:String / Name:String] </ programText >
		if notBool $hasMapping(Env:Map, Name:String)
		[structural] 
	
	op resolve : K -> K 
	rule
		< k > (. => resolve(Tu:K)) ~> resolveReferences ...</ k >
		< translationUnits >... BagItem(Tu:K) => . ...</ translationUnits >
		[structural] 
	rule
		< k > resolveReferences => . ...</ k >
		< translationUnits > (.).Bag </ translationUnits >
		[structural] 
		
	op resolveInternal : Id K K -> K 
	op resolveExternal : Id K Bag K -> K 
	op resolveExternal-aux : Id K Bag K Nat K -> K [metadata "strict(6)"] 
	
	op recordFunctionTranslationUnitInformation : K Type K K -> K --- name, type, context, where defined
	rule
		< k > recordFunctionTranslationUnitInformation(X:Id, T:Type, Tu:K, DefTu:K) => . ...</ k >
		< functionTranslationUnits >... Tu:K |-> Map((Funs:Map => Funs:Map[DefTu:K / X:Id])) ...</ functionTranslationUnits >
		if hasFunctionType(T:Type)
		[structural] 
	rule
		< k > recordFunctionTranslationUnitInformation(?, T:Type, ?, ?) => . ...</ k >
		if notBool hasFunctionType(T:Type)
		[structural] 
	
	--- fixme
	--- should be adding to env after figuring initializer
	--- should be changing env to be correct env before figuring initializer
	op allocateWithInit : K Nat -> K [metadata "strict"] 
	op noAllocateWithInit : K Nat -> K [metadata "strict"] 
	op resolveInternal-aux : Id K K K -> K [metadata "strict(4)"] 
	rule
		< k > resolveInternal(X:Id, Tu:K, declarationObject(T:Type, Tu:K, K:K))
			=> resolveInternal-aux(X:Id, Tu:K, declarationObject(T:Type, Tu:K, K:K), figureInitializer(X:Id, T:Type, K:K))
		...</ k >
		< currentTranslationUnit > ? => Tu:K </ currentTranslationUnit >
		[structural] 
	rule
		< k > resolveInternal-aux(X:Id, Tu:K, declarationObject(?, Tu:K, ?), initializerValue(X:Id, T:Type, K:K))
			=> allocateType(Loc:Nat, T:Type)
			~> addToEnv(X:Id, Loc:Nat)
			~> giveType(X:Id, T:Type)
			~> initialize(X:Id, T:Type, K:K)
			~> recordFunctionTranslationUnitInformation(X:Id, T:Type, Tu:K, Tu:K)
		...</ k >
		< nextLoc > Loc:Nat => inc(Loc:Nat) </ nextLoc >
		< currentTranslationUnit > ? => Tu:K </ currentTranslationUnit >
		[structural] 
			
	rule
		< k > resolveExternal(X:Id, Tu:K, Units:Bag, declarationObject(T:Type, DefTu:K, K:K))
			=> resolveExternal-aux(X:Id, Tu:K, Units:Bag, declarationObject(T:Type, DefTu:K, K:K), Loc:Nat, figureInitializer(X:Id, T:Type, K:K))
		...</ k >
		< nextLoc > Loc:Nat => inc(Loc:Nat) </ nextLoc >
		[structural] 
	rule
		< k > ( .K
			=> addToEnv(X:Id, Loc:Nat)
			~> giveType(X:Id, T:Type)
			~> recordFunctionTranslationUnitInformation(X:Id, T:Type, Tu':K, DefTu:K)
			) ~> resolveExternal-aux(X:Id, Tu:K, ((BagItem(Tu':K) => .) Units:Bag), declarationObject(?, DefTu:K, ?), Loc:Nat, initializerValue(X:Id, T:Type, K:K))
		...</ k >
		< currentTranslationUnit > ? => Tu':K </ currentTranslationUnit >
		< preLinkage >... Tu':K |-> Map((? (X:Id |-> external => .))) ...</ preLinkage >
		[structural] 
	rule
		< k > resolveExternal-aux(X:Id, Tu:K, (.).Bag, declarationObject(?, DefTu:K, ?), Loc:Nat, initializerValue(X:Id, T:Type, K:K))
			=> allocateType(Loc:Nat, T:Type)
			~> addToEnv(X:Id, Loc:Nat)
			~> giveType(X:Id, T:Type)
			~> initialize(X:Id, T:Type, K:K)
			~> recordFunctionTranslationUnitInformation(X:Id, T:Type, Tu:K, DefTu:K)
		...</ k >
		< currentTranslationUnit > ? => Tu:K </ currentTranslationUnit >
		< externalLocations > Locs:Map => Locs:Map[Loc:Nat / X:Id] </ externalLocations >
		if notBool $hasMapping(Locs:Map, X:Id)
		[structural] 
	rule
		< k > resolveExternal-aux(X:Id, ?, ((BagItem(Tu:K) => .) Units:Bag), ?, ?, ?) ...</ k >
		< preLinkage >... Tu:K |-> Map(M:Map) ...</ preLinkage >
		if notBool $hasMapping(M:Map, X:Id)
		[structural] 
	rule
		< k > resolveExternal-aux(X:Id, ?, ((BagItem(Tu:K) => .) Units:Bag), ?, ?, ?) ...</ k >
		< preLinkage >... Tu:K |-> Map((? X:Id |-> internal)) ...</ preLinkage >
		[structural] 
	
	--- 
	rule
		< k > (. => resolveInternal(X:Id, Tu:K, K:K)) ~> resolve(Tu:K) ...</ k >
		< preLinkage >... Tu:K |-> Map((? (X:Id |-> internal => .))) ...</ preLinkage >
		< internalDefinitions >... Tu:K |-> Map((? (X:Id |-> K:K => .))) ...</ internalDefinitions >
		< declarationOrder >... Tu:K |-> ListToK((ListItem(X:Id) => .) ?) ...</ declarationOrder >
		[structural] 
		
	--- static variable without an initializer
	rule
		< k > (. => resolveInternal(X:Id, Tu:K, declarationObject(unqualifyType(T:Type), Tu:K, initializer(zero(X:Id))))) ~> resolve(Tu:K) ...</ k >
		< preLinkage >... Tu:K |-> Map((? (X:Id |-> internal => .))) ...</ preLinkage >
		< internalDefinitions >... Tu:K |-> Map(Defs:Map) ...</ internalDefinitions >
		< declarationOrder >... Tu:K |-> ListToK((ListItem(X:Id) => .) ?) ...</ declarationOrder >
		< preTypes >... Tu:K |-> Map((? (X:Id |-> T:Type => .))) ...</ preTypes >
		if notBool $hasMapping(Defs:Map, X:Id)
		[structural] 
		
	rule
		< k > (. => resolveExternal(X:Id, Tu:K, Units:Bag, K:K)) ~> resolve(Tu:K) ...</ k >
		< preLinkage >... Tu:K |-> Map((? (X:Id |-> external => .))) ...</ preLinkage >
		< externalDefinitions > ExtDefs:Map (X:Id |-> K:K => .) </ externalDefinitions >
		< declarationOrder >... Tu:K |-> ListToK((ListItem(X:Id) => .) ?) ...</ declarationOrder >
		< translationUnits > Units:Bag </ translationUnits >
		if notBool $hasMapping(ExtDefs:Map, X:Id)
		[structural] 

	eq toString(Identifier(S:String)) = S:String 
	eq toString(S:String) = S:String 
	eq toString(Num:Nat) = Int2String(Num:Nat) 
	eq Rat2String(sym(N:Nat), M:NzNat) = "sym(" +String Rat2String(N:Nat, M:NzNat) +String ")" 
	
	--- fixme this means we've declared it twice (like a prototype maybe?), but already handled it.  happening with getc in clib.c
	rule
		< k > resolve(Tu:K) ...</ k >
		< preLinkage >... Tu:K |-> Map(Linkage:Map) ...</ preLinkage >
		< declarationOrder >... Tu:K |-> ListToK((ListItem(X:Id) => .) ?) ...</ declarationOrder >
		< externalDefinitions > ExtDefs:Map </ externalDefinitions >
		< internalDefinitions > IntDefs:Map </ internalDefinitions >
		if notBool $hasMapping(Linkage:Map, X:Id)
		andBool notBool $hasMapping(ExtDefs:Map, X:Id)
		andBool notBool $hasMapping(IntDefs:Map, X:Id)
		[structural] 
	
	--- function prototypes
	rule
		< k > (. => 
				giveType(X:Id, T:Type)
				~> recordFunctionTranslationUnitInformation(X:Id, T:Type, Tu:K, Tu:K)  --- fixme fake Tu
			)
			~> resolve(Tu:K) 
		...</ k >
		< currentTranslationUnit > ? => Tu:K </ currentTranslationUnit >
		< preLinkage >... Tu:K |-> Map((? (X:Id |-> external => .))) ...</ preLinkage >
		< preTypes >... Tu:K |-> Map((? X:Id |-> prototype(T:Type))) ...</ preTypes >
		< declarationOrder >... Tu:K |-> ListToK((ListItem(X:Id) => .) ?) ...</ declarationOrder >
		< externalDefinitions > Defs:Map </ externalDefinitions >
		if hasFunctionType(T:Type)
		andBool notBool $hasMapping(Defs:Map, X:Id)
		[structural] 
		
	--- c1x 6.9.2:2 A declaration of an identifier for an object that has file scope without an initializer, and without a storage-class specifier or with the storage-class specifier static, constitutes a tentative definition. If a translation unit contains one or more tentative definitions for an identifier, and the translation unit contains no external definition for that identifier, then the behavior is exactly as if the translation unit contains a file scope declaration of that identifier, with the composite type as of the end of the translation unit, with an initializer equal to 0
	rule
		< k > (. 
			=> allocateType(Loc:Nat, unqualifyType(T:Type))
			~> addToEnv(X:Id, Loc:Nat)
			~> giveType(X:Id, unqualifyType(T:Type))
			~> zero(X:Id)
			) ~> resolve(Tu:K)
		...</ k >
		< preLinkage >... Tu:K |-> Map((? (X:Id |-> external => .))) ...</ preLinkage >
		< preTypes >... Tu:K |-> Map((? X:Id |-> T:Type)) ...</ preTypes >
		< declarationOrder >... Tu:K |-> ListToK((ListItem(X:Id) => .) ?) ...</ declarationOrder >
		< externalDefinitions > Defs:Map </ externalDefinitions >
		< currentTranslationUnit > ? => Tu:K </ currentTranslationUnit >
		< nextLoc > Loc:Nat => inc(Loc:Nat) </ nextLoc >
		< externalLocations > Locs:Map => Locs:Map[Loc:Nat / X:Id] </ externalLocations >
		if notBool $hasMapping(Locs:Map, X:Id)
		andBool notBool hasFunctionType(T:Type)
		andBool notBool hasIncompleteType(T:Type)
		andBool notBool hasExternType(T:Type)
		andBool notBool $hasMapping(Defs:Map, X:Id)
		[structural] 
	rule
		< k > resolve(Tu:K) ...</ k >
		< preLinkage >... Tu:K |-> Map((? (X:Id |-> external => .))) ...</ preLinkage >
		< preTypes >... Tu:K |-> Map((? X:Id |-> T:Type)) ...</ preTypes >
		< declarationOrder >... Tu:K |-> ListToK((ListItem(X:Id) => .) ?) ...</ declarationOrder >
		< externalDefinitions > Defs:Map </ externalDefinitions >
		if notBool hasFunctionType(T:Type)
		andBool hasExternType(T:Type)
		andBool notBool $hasMapping(Defs:Map, X:Id)
		[structural] 
		
	rule
		< k > resolve(Tu:K) => . ...</ k >
		< preLinkage >... Tu:K |-> Map(.) ...</ preLinkage >
		< internalDefinitions >... Tu:K |-> Map(.) ...</ internalDefinitions >
		< declarationOrder >... Tu:K |-> ListToK((.).List) ...</ declarationOrder >
		[structural] 
				
	--- need to worry about things that don't have definitions that may override externs
	--- want to make it so env is always correct local env, so need to have a set of global envs, one for each tu
endkm

kmod COMMON-SEMANTICS-DECLARATIONS-ENUMS is
	including COMMON-SEMANTICS-DECLARATIONS-INCLUDE 
	
	op fillEnums : K -> K 
	op fillEnums : K K -> K 
	rule
		< k > EnumDef(X:Id, L:List{C}) => fillEnums(EnumDef(X:Id, L:List{C})) ...</ k >
		[structural] 
	rule < k > fillEnums(K:K) => fillEnums(K:K, 0) ...</ k > 
	rule
		< k > fillEnums(EnumDef(X:Id, EnumItemLoc(EnumItem(E:Id, emptyValue), Loc:K) :: L:List{C}), K:K) 
			=> EnumItemLoc(declare(typedDeclaration(int, E:Id), SingleInit(K:K)), Loc:K)
			~> fillEnums(EnumDef(X:Id, L:List{C}), K:K + tv(1, int))
		...</ k >
		[structural] 
	rule
		< k > fillEnums(EnumDef(X:Id, EnumItemLoc(EnumItem(E:Id, Exp:K), Loc:K) :: L:List{C}), ?) 
			=> EnumItemLoc(declare(typedDeclaration(int, E:Id), SingleInit(Exp:K)), Loc:K)
			~> fillEnums(EnumDef(X:Id, L:List{C}), Exp:K + 1)
		...</ k >
		if Exp:K =/=Bool NothingExpression
		[structural] 
	rule
		< k > fillEnums(EnumDef(X:Id, Nil), ?) => .K ...</ k > 
		[structural] 
endkm

kmod COMMON-C-DECLARATIONS is
	including COMMON-SEMANTICS-DECLARATIONS-INCLUDE 
	
	including COMMON-SEMANTICS-DECLARATIONS-BINDING 
	including COMMON-SEMANTICS-DECLARATIONS-GENERAL 
	including COMMON-SEMANTICS-DECLARATIONS-INITIALIZATIONS 
	including COMMON-SEMANTICS-DECLARATIONS-ENUMS 
	including COMMON-SEMANTICS-DECLARATIONS-RESOLUTION 
endkm
