kmod COMMON-SEMANTICS-EXPRESSIONS-INCLUDE is
	including COMMON-INCLUDE 
	op assign : K K -> K 
	op compoundLiteral : Nat -> Id 
endkm

--- i'm just playing around here
kmod COMMON-SEMANTICS-ABSTRACTION is
	including COMMON-INCLUDE 
	
	--- op F-abs : Nat -> Nat --- unique #
	--- op F-hasType : BaseValue Type -> Formula 
	--- op F-eq : K K -> Formula 
	--- op F-cast : K Type Type -> Formula 
	--- rule
		--- < k > Identifier("__freshChar")
			--- => tv(F-abs(N:Nat), char)
		--- ...</ k >
		--- < freshNat > N:Nat => sNat(N:Nat) </ freshNat >
		--- < formula >... . => 
			--- F-hasType(F-abs(N:Nat), char) 
			--- /\ F-eq(Identifier("__freshChar"), F-abs(N:Nat)) 
		--- ...</ formula >
		--- [structural] 
		
	--- rule
		--- < k > cast(T:Type, tv(F-abs(N':Nat), T':Type))
			--- => tv(F-abs(N:Nat), T:Type)
		--- ...</ k >
		--- < freshNat > N:Nat => sNat(N:Nat) </ freshNat >
		--- < formula >... . =>  
			--- F-eq(F-cast(F-abs(N':Nat), T:Type, T':Type), F-abs(N:Nat))
		--- ...</ formula >
		--- [structural] 
endkm

kmod COMMON-SEMANTICS-COMPOUND-LITERAL is
	including COMMON-SEMANTICS-EXPRESSIONS-INCLUDE 
	
	op handleCompoundLiteral : K -> K [metadata "strict"] 
	
	--- comes back from figureInit as initializerValue(id, type, inits)
	rule
		< k > CompoundLiteral(N:Nat, T:Type, K:K, Init:K)
			=> handleCompoundLiteral(figureInitializer(compoundLiteral(N:Nat), DeclType(T:Type, K:K), Init:K))
		...</ k >
		[structural] 
		
	rule
		< k > handleCompoundLiteral(initializerValue(X:Id, T:Type, Init:K))
			=> allocateType(Loc:Nat, T:Type)
			~> addToEnv(X:Id, Loc:Nat)
			~> giveType(X:Id, T:Type)
			~> initialize(X:Id, T:Type, Init:K)
			~> X:Id
		...</ k >
		< compoundLiteralMap > M:Map => M:Map[Loc:Nat / X:Id] </ compoundLiteralMap >
		< nextLoc > Loc:Nat => inc(Loc:Nat) </ nextLoc >
		if notBool $hasMapping(M:Map, X:Id)
		[structural] 
		
	rule
		< k > handleCompoundLiteral(initializerValue(X:Id, T:Type, Init:K))
			=> addToEnv(X:Id, Loc:Nat)
			~> giveType(X:Id, T:Type)
			~> initialize(X:Id, T:Type, Init:K)
			~> X:Id
		...</ k >
		< compoundLiteralMap >... X:Id |-> Loc:Nat </ compoundLiteralMap >
		[structural] 
endkm

kmod COMMON-SEMANTICS-BOOLEAN is
	including COMMON-INCLUDE 
	
	--- rule
		--- < k > tv(0, ?) || E:Expression => sequencePoint ~> E:Expression ? tv(1, int) : tv(0, int) ...</ k >
		--- [structural] 
	--- rule
		--- < k > tv(N:Nat, ?) || E:Expression => sequencePoint ~> tv(1, int) ...</ k >
		--- if N:Nat =/=Bool 0
		--- [structural] 
		
	--- rule
		--- < k > tv(0, ?) && E:Expression => sequencePoint ~> tv(0, int) ...</ k >
		--- [structural] 
	--- rule
		--- < k > tv(N:Nat, ?) && E:Expression => sequencePoint ~> E:Expression ? tv(1, int) : tv(0, int)  ...</ k >
		--- if N:Nat =/=Bool 0
		--- [structural] 
	
	--- make sure sequence points are maintained properly
	
	
	rule
		< k > E1:K || E:Expression
			=> E1:K ? tv(1, int) : (E:Expression ? tv(1, int) : tv(0, int))
		...</ k >
		[structural] 
	rule
		< k > E1:K && E:Expression 
			=> E1:K ? (E:Expression ? tv(1, int) : tv(0, int)) : tv(0, int)
		...</ k >
		[structural] 
	
	--- FIXME the types of these results are wrong.  The correct behavior is quite complicated.  see 6.5.15
	--- rule
		--- < k > tv(N:Nat, ?) ? E1:Expression : E2:Expression => sequencePoint ~> E1:Expression ...</ k >
		--- if N:Nat =/=Bool 0
		--- [structural] 
		
	--- rule
		--- < k > tv(0, ?) ? E1:Expression : E2:Expression => sequencePoint ~> E2:Expression ...</ k >
		--- [structural] 
	rule
		< k > E:K ? E1:Expression : E2:Expression 
			=> IfThenElse(E:K, E1:Expression, E2:Expression) 
		...</ k >
		[structural]
		
	
	--- rule !(tv(V:BaseValue, ?)) => tv(0, int)
		--- if V:BaseValue =/=Bool 0
		--- [structural] 
	--- rule !(tv(V:BaseValue, ?)) => tv(1, int)
		--- if (V:BaseValue ==Bool 0)
		--- [structural] 
		
	--- c1x 6.5.3.3:5 The expression !E is equivalent to (0==E)
	rule !(E:K) => tv(0, int) == E:K
		[structural] 
	--- rule !(tv(V:BaseValue, ?)) => tv(1, int)
		--- if (V:BaseValue ==Bool 0)
		--- [structural] 
endkm

kmod COMMON-SEMANTICS-SIZEOF is
	including COMMON-INCLUDE 
	
	eq sizeofType(T:Type) = cast(cfg:sizeut, byteSizeofType(T:Type)) 
	op byteSizeofTypeAux : K -> K [metadata "strict"] 
	eq byteSizeofType(T:Type) = byteSizeofTypeAux(bitSizeofType(T:Type)) 
	ceq byteSizeofTypeAux(tv(N:Nat, T:Type)) = tv(bitsToBytes(N:Nat), T:Type)
		if T:Type ==Bool cfg:largestUnsigned 
	
	rule
		< k > SizeofExpression(E:Expression) => sizeofType(typeof(E:Expression)) ...</ k >
		[structural] 
	rule
		< k > SizeofType(T:Type, K:K) => sizeofType(DeclType(T:Type, K:K)) ...</ k >
		[structural] 
	
	op bitSizeofList : List{Type} -> K 
	eq bitSizeofList(T:Type :: L:List{Type}) = bitSizeofType(T:Type) + bitSizeofList(L:List{Type}) 
	eq bitSizeofList(Nil) = 0 
	
	op maxBitSizeofList : List{Type} -> K 
	op maxBitSizeofList-aux : List{Type} Nat -> K 
	eq maxBitSizeofList(L:List{Type}) = maxBitSizeofList-aux(L:List{Type}, 0) 
	rule
		< k > maxBitSizeofList-aux(T:Type :: L:List{Type}, N:Nat) 
			=> bitSizeofType(T:Type) ~> maxBitSizeofList-aux(L:List{Type}, N:Nat) 
		...</ k >
		[structural] 
	rule
		< k > (tv(N':Nat, ?) => .) ~> maxBitSizeofList-aux(L:List{Type}, (N:Nat => maxNat(N:Nat, N':Nat))) ...</ k >
		[structural] 
	rule
		< k > maxBitSizeofList-aux(Nil, N:Nat) => N:Nat ...</ k >
		[structural] 
	
	eq bitSizeofType(arrayType(T:Type, N:Nat)) = bitSizeofType(T:Type) * N:Nat 
	eq bitSizeofType(flexibleArrayType(T:Type)) = 0 
	eq bitSizeofType(functionType(?, ?)) = numBitsPerByte 
	eq bitSizeofType(T:BaseType) = numBits(T:BaseType) 
	eq bitSizeofType(pointerType(?)) = cfg:ptrsize *Nat numBitsPerByte 
	eq bitSizeofType(typedDeclaration(T:Type, ?)) = bitSizeofType(T:Type) 
	eq bitSizeofType(bitfieldType(?, N:Nat)) = N:Nat 
	eq bitSizeofType(qualifiedType(T:Type, ?)) = bitSizeofType(T:Type) 
	--- eq bitSizeofType(prototype(T:Type)) = bitSizeofType(T:Type) 
	rule
		< k > bitSizeofType(structType(X:Id)) => bitSizeofList(L:List{Type}) ...</ k >
		< structs >... X:Id |-> L:List{Type} ...</ structs >
		[structural] 
	rule
		< k > bitSizeofType(unionType(X:Id)) => maxBitSizeofList(L:List{Type}) ...</ k >
		< structs >... X:Id |-> L:List{Type} ...</ structs >
		[structural] 
	
	--- ---C99 6.2.6.1:26 ... Each unqualified type has several qualified versions of its type,40) corresponding to the combinations of one, two, or all three of the const, volatile, and restrict qualifiers. The qualified or unqualified versions of a type are distinct types that belong to the same type category and have the same representation and alignment requirements. ..
	--- eq sizeofType(qualifiedType(T:Type, ?)) = sizeofType(T:Type) .	

endkm

kmod COMMON-SEMANTICS-IDENTIFIERS is
	including COMMON-SEMANTICS-EXPRESSIONS-INCLUDE 
	
	--- 6.3.2.2 Except when it is the operand of the sizeof operator, the unary & operator, the ++ operator, the -- operator, or the left operand of the . operator or an assignment operator, an lvalue that does not have an array type is converted to the value stored in the designated object (and is no longer an lvalue)

	--- generic lookup
	rule [lookup]:
		< k > X:Id => read(Loc:Nat, T:Type) ...</ k >
		< env >... X:Id |-> Loc:Nat ...</ env >
		< types >... X:Id |-> T:Type ...</ types >
		if notBool(hasArrayType(T:Type)) andBool notBool(hasFunctionType(T:Type))
		[structural] --- nondet
		
	---C99 6.3.2.1:3 Except when it is the operand of the sizeof operator or the unary & operator, or is a string literal used to initialize an array, an expression that has type "array of type" is converted to an expression with type "pointer to type" that points to the initial element of the array object and is not an lvalue. If the array object has register storage class, the behavior is undefined
	
	--- fixme i wish i didn't have to make this a pointertype directly.  
	--- rule [lookup-array]:
		--- < k > X:Id => tv(Loc:Nat, T:Type) ...</ k >
		--- < env >... X:Id |-> Loc:Nat ...</ env >
		--- < types >... X:Id |-> T:Type ...</ types >
		--- if hasArrayType(T:Type)
		--- [structural] 
	rule [lookup-array]:
		< k > X:Id => tv(Loc:Nat, pointerType(innerType(T:Type))) ...</ k >
		< env >... X:Id |-> Loc:Nat ...</ env >
		< types >... X:Id |-> T:Type ...</ types >
		if hasArrayType(T:Type)
		[structural] 
		
	---C99 6.3.2.1:4 A function designator is an expression that has function type.  Except when it is the operand of the sizeof operator or the unary & operator, a function designator with type "function returning T" is converted to an expression that has type "pointer to a function returning T"
	rule [lookup-closure]:
		< k > X:Id => tv(Loc:Nat, pointerType(functionType(T:Type, L:List{Type}))) ...</ k >
		< env >... X:Id |-> Loc:Nat ...</ env >
		< types >... X:Id |-> functionType(T:Type, L:List{Type}) ...</ types >
		[structural] 
		
	rule [lookup-builtin-function]:
		< k > X:Id => tv(functionPrototype(X:Id, functionType(T:Type, L:List{Type})), functionType(T:Type, L:List{Type})) ...</ k >
		< env > Env:Map </ env >
		< types >... X:Id |-> functionType(T:Type, L:List{Type}) ...</ types >
		if notBool $hasMapping(Env:Map, X:Id)
		[structural] 
endkm

kmod COMMON-SEMANTICS-FUNCTION-CALLS is
	including COMMON-SEMANTICS-EXPRESSIONS-INCLUDE 

	op application : K List{C} -> K [metadata "strict(1)"] 
	
	--- this must enforce arguments are evaluated
	--- using List{Type} until I fix syntax types
	rule [function-application-pre]:
		< k > Call(tv(Loc:Nat, pointerType(T:Type)), L:List{Type}) 
			=> application(readFunction(Loc:Nat), L:List{Type}) 
		...</ k >
		if hasFunctionType(T:Type)
		[metadata "computational"] 
		
	rule [function-application-builtin-pre]:
		< k > Call(tv(functionPrototype(X:Id, T:Type), T:Type), L:List{Type})
			=> application(functionPrototype(X:Id, T:Type), L:List{Type}) 
		...</ k >
		if hasFunctionType(T:Type)
		andBool builtinIdentifiers contains X:Id
		[metadata "computational"] 

	op populateFromGlobal : -> K 
	--- fixme: this must be a rule because of the rules associated with declaring local and bound variables
	rule [populateFromGlobal]:
		< k > populateFromGlobal => .K ...</ k >
		< genv >... Tu:K |-> Map(G:Map) ...</ genv > < env > ? => G:Map </ env >
		< gtypes >... Tu:K |-> Map(GT:Map) ...</ gtypes > < types > ? => GT:Map </ types >
		< gstructs > GS:Map </ gstructs > < structs > ? => GS:Map </ structs >
		< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		[structural] 
		
	op resetNestingDepth : -> K 
	rule
		< k > resetNestingDepth => .K ...</ k > 
		--- < nestingDepth > ? => 1 </ nestingDepth >
		[structural] 

	rule [builtin-application]:
		< k > application(functionPrototype(X:Id, T:Type), L:List{C})
			=> application(functionObject(X:Id, T:Type, handleBuiltin(X:Id, T:Type)), L:List{C})
		...</ k >
		[structural] 
		
		
	rule [function-application]:
		(< control >
			< k > application(functionObject(X:Id, functionType(R:Type, P:List{Type}), B:K), L:List{C}) ~> K:K </ k >
			< currentTranslationUnit > OldTu:K </ currentTranslationUnit >
		C:Bag
		</ control >
		=>
		< control >
			< k > sequencePoint ~> populateFromGlobal ~> resetNestingDepth ~> bind(L:List{C}, P:List{Type}) ~> B:K ~> Return(NothingExpression) </ k >
			< currentFunction > X:Id </ currentFunction >
			< currentTranslationUnit > Tu:K </ currentTranslationUnit >
		...</ control >)
		< callStack > (.).List => List(< stackFrame > C:Bag < continuation > K:K </ continuation > < currentTranslationUnit > OldTu:K </ currentTranslationUnit > </ stackFrame >) ...</ callStack >
		< functionTranslationUnits >... OldTu:K |-> Map((? X:Id |-> Tu:K)) ...</ functionTranslationUnits >
		[metadata "computational"] --- nondet
endkm

kmod COMMON-SEMANTICS-ARRAY-SUBSCRIPTING is
	including COMMON-SEMANTICS-EXPRESSIONS-INCLUDE 
	--- can't be done everywhere because same syntax as in declarations
	rule < k > E1:Expression[E2:Expression] => *(E1:Expression + E2:Expression) ...</ k > 
		[structural] 
endkm

kmod COMMON-SEMANTICS-LITERALS is
	including COMMON-SEMANTICS-EXPRESSIONS-INCLUDE 
	
	--- +1 for terminating 0
	--- alloc(Loc:Nat, lengthString(S:String) +Nat 1) ~> 
	rule [const-string-notfound]:
		< k > (. => allocString(Loc:Nat, S:String +String "\0"))
			~> StringLiteral(S:String)
		...</ k >
		< nextLoc > Loc:Nat => inc(Loc:Nat) </ nextLoc >
		< statics > M:Map (. => S:String |-> tv(Loc:Nat, arrayType(char, lengthString(S:String) +Nat 1))) </ statics >
		if notBool($hasMapping(M:Map, S:String))
		[structural] 
		
	--- fixme should make type const
	rule [const-string-found]:
		< k > StringLiteral(S:String) => tv(N:Nat, pointerType(T:Type)) ...</ k >
		< statics >... S:String |-> tv(N:Nat, arrayType(T:Type, ?)) ...</ statics >
		[structural] 
	
	---c99 6.4.4.1:5 The type of an integer constant is the first of the corresponding list in which its value can be represented
***(
											Octal or Hexadecimal 
Suffix			Decimal Constant			Constant
------------------------------------------------------------------
none			int							int
				long int					unsigned int
				long long int				long int
											unsigned long int
											long long int
											unsigned long long int
------------------------------------------------------------------
u or U			unsigned int 				unsigned int
				unsigned long int 			unsigned long int
				unsigned long long int 		unsigned long long int
------------------------------------------------------------------
l or L			long int 					long int
				long long int 				unsigned long int
											long long int
											unsigned long long int
------------------------------------------------------------------
Both u or U		unsigned long int 			unsigned long int
and l or L 		unsigned long long int 		unsigned long long int
------------------------------------------------------------------
ll or LL 		long long int				long long int
											unsigned long long int
------------------------------------------------------------------
Both u or U		unsigned long long int 		unsigned long long int
and ll or LL
------------------------------------------------------------------
***)
	---c99 6.4.4.1:6 If an integer constant cannot be represented by any type in its list, it may have an extended integer type, if the extended integer type can represent its value. If all of the types in the list for the constant are signed, the extended integer type shall be signed. If all of the types in the list for the constant are unsigned, the extended integer type shall be unsigned. If the list contains both signed and unsigned types, the extended integer type may be signed or unsigned. If an integer constant cannot be represented by any type in its list and has no extended integer type, then the integer constant has no type
	---c99 6.2.5:4 ... There may also be impleme
	
	--- c1x 6.4.4.4:10
	eq CharLiteral(N:Nat) = tv(N:Nat, int) 
	eq IntLiteral(V:Value) = V:Value 
	eq FloatLiteral(V:Value) = V:Value 
	eq Constant(V:Value) = V:Value 
	--- rule < k > N:Nat => tv(N:Nat, bignum) ...</ k > --- for internal computations
	rule < k > N:Nat => tv(N:Nat, cfg:largestUnsigned) ...</ k > 
		[structural] --- for internal computations
		
	rule NoSuffix(DecimalConstant(I:Int)) => 
		if ((I:Int <=Int max(int)) andBool (I:Int >=Int min(int))) then tv(I:Int, int) else
		if ((I:Int <=Int max(long-int)) andBool (I:Int >=Int min(long-int))) then tv(I:Int, long-int) else
		if ((I:Int <=Int max(long-long-int)) andBool (I:Int >=Int min(long-long-int))) then tv(I:Int, long-long-int) else 
			tv(I:Int, no-type)
		fi fi fi
		[structural] 
		
	op simplifyForHex : String -> String 
	ceq simplifyForHex(S:String) = simplifyForHex(butFirstChar(S:String))
		if firstChar(S:String) ==Bool "0"
		andBool lengthString(S:String) >Nat 1 
	ceq simplifyForHex(S:String) = S:String
		if firstChar(S:String) =/=Bool "0" 
		orBool lengthString(S:String) ==Bool 1 
		
		
	op hexOrOctalConstant : K -> K 
	eq HexConstant(S:String) = hexOrOctalConstant(String2Rat(simplifyForHex(S:String), 16)) 
	eq OctalConstant(I:Int) = hexOrOctalConstant(truncRat(String2Rat(Rat2String(I:Int, 10), 8))) 
	
	rule NoSuffix(hexOrOctalConstant(I:Int)) =>
		if ((I:Int <=Int max(int)) andBool (I:Int >=Int min(int))) then tv(I:Int, int) else
		if ((I:Int <=Int max(unsigned-int)) andBool (I:Int >=Int min(unsigned-int))) then tv(I:Int, unsigned-int) else
		if ((I:Int <=Int max(long-int)) andBool (I:Int >=Int min(long-int))) then tv(I:Int, long-int) else
		if ((I:Int <=Int max(unsigned-long-int)) andBool (I:Int >=Int min(unsigned-long-int))) then tv(I:Int, unsigned-long-int) else
		if ((I:Int <=Int max(long-long-int)) andBool (I:Int >=Int min(long-long-int))) then tv(I:Int, long-long-int) else 
		if ((I:Int <=Int max(unsigned-long-long-int)) andBool (I:Int >=Int min(unsigned-long-long-int))) then tv(I:Int, unsigned-long-long-int) else
			tv(I:Int, no-type)
		fi fi fi fi fi fi
		[structural] 

	rule U(hexOrOctalConstant(I:Int)) =>
		if ((I:Int <=Int max(unsigned-int)) andBool (I:Int >=Int min(unsigned-int))) then tv(I:Int, unsigned-int) else
		if ((I:Int <=Int max(unsigned-long-int)) andBool (I:Int >=Int min(unsigned-long-int))) then tv(I:Int, unsigned-long-int) else
		if ((I:Int <=Int max(unsigned-long-long-int)) andBool (I:Int >=Int min(unsigned-long-long-int))) then tv(I:Int, unsigned-long-long-int) else
			tv(I:Int, no-type)
		fi fi fi
		[structural] 
		
	rule L(hexOrOctalConstant(I:Int)) =>
		if ((I:Int <=Int max(long-int)) andBool (I:Int >=Int min(long-int))) then tv(I:Int, long-int) else
		if ((I:Int <=Int max(unsigned-long-int)) andBool (I:Int >=Int min(unsigned-long-int))) then tv(I:Int, unsigned-long-int) else
		if ((I:Int <=Int max(long-long-int)) andBool (I:Int >=Int min(long-long-int))) then tv(I:Int, long-long-int) else 
		if ((I:Int <=Int max(unsigned-long-long-int)) andBool (I:Int >=Int min(unsigned-long-long-int))) then tv(I:Int, unsigned-long-long-int) else
			tv(I:Int, no-type)
		fi fi fi fi
		[structural] 
		
	rule UL(hexOrOctalConstant(I:Int)) =>
		if ((I:Int <=Int max(unsigned-long-int)) andBool (I:Int >=Int min(unsigned-long-int))) then tv(I:Int, unsigned-long-int) else
		if ((I:Int <=Int max(unsigned-long-long-int)) andBool (I:Int >=Int min(unsigned-long-long-int))) then tv(I:Int, unsigned-long-long-int) else
			tv(I:Int, no-type)
		fi fi
		[structural] 
		
	rule LL(hexOrOctalConstant(I:Int)) =>
		if ((I:Int <=Int max(long-long-int)) andBool (I:Int >=Int min(long-long-int))) then tv(I:Int, long-long-int) else 
		if ((I:Int <=Int max(unsigned-long-long-int)) andBool (I:Int >=Int min(unsigned-long-long-int))) then tv(I:Int, unsigned-long-long-int) else
			tv(I:Int, no-type)
		fi fi
		[structural] 
	
	rule ULL(hexOrOctalConstant(I:Int)) =>
		if ((I:Int <=Int max(unsigned-long-long-int)) andBool (I:Int >=Int min(unsigned-long-long-int))) then tv(I:Int, unsigned-long-long-int) else
			tv(I:Int, no-type)
		fi
		[structural] 
		
		
	rule U(DecimalConstant(I:Int)) => 
		if ((I:Int <=Int max(unsigned-int)) andBool (I:Int >=Int min(unsigned-int))) then tv(I:Int, unsigned-int) else
		if ((I:Int <=Int max(unsigned-long-int)) andBool (I:Int >=Int min(unsigned-long-int))) then tv(I:Int, unsigned-long-int) else
		if ((I:Int <=Int max(unsigned-long-long-int)) andBool (I:Int >=Int min(unsigned-long-long-int))) then tv(I:Int, unsigned-long-long-int) else 
			tv(I:Int, no-type)
		fi fi fi
		[structural] 
	rule L(DecimalConstant(I:Int)) => 
		if ((I:Int <=Int max(long-int)) andBool (I:Int >=Int min(long-int))) then tv(I:Int, long-int) else
		if ((I:Int <=Int max(long-long-int)) andBool (I:Int >=Int min(long-long-int))) then tv(I:Int, long-long-int) else
			tv(I:Int, no-type)
		fi fi
		[structural] 
	rule UL(DecimalConstant(I:Int)) => 
		if ((I:Int <=Int max(unsigned-long-int)) andBool (I:Int >=Int min(unsigned-long-int))) then tv(I:Int, unsigned-long-int) else
		if ((I:Int <=Int max(unsigned-long-long-int)) andBool (I:Int >=Int min(unsigned-long-long-int))) then tv(I:Int, unsigned-long-long-int) else
			tv(I:Int, no-type)
		fi fi		
		[structural] 
	rule LL(DecimalConstant(I:Int)) => 
		if ((I:Int <=Int max(long-long-int)) andBool (I:Int >=Int min(long-long-int))) then tv(I:Int, long-long-int) else
			tv(I:Int, no-type)
		fi
		[structural] 
	rule ULL(DecimalConstant(I:Int)) => 
		if ((I:Int <=Int max(unsigned-long-long-int)) andBool (I:Int >=Int min(unsigned-long-long-int))) then tv(I:Int, unsigned-long-long-int) else
			tv(I:Int, no-type)
		fi
		[structural] 
		
		
		
	--- FloatLiteral(L(HexFloatConstant(256, 46117495616, 2)))
	
	--- op _^Rat_ : NzRat Int -> NzRat [ditto] 
	--- op _^Rat_ : Rat Int -> Rat [ditto] 
	--- ceq R:NzRat ^Rat I:Int = 1 /Rat (R:NzRat ^Rat absInt(I:Int))
		--- if I:Int <Int 0 
	--- ceq 0 ^Rat I:Int = 0
		--- if I:Int <Int 0 
	
	--- FIXME
	--- eq HexFloatConstant(?, ?, ?, F:Float) = DecimalFloatConstant(F:Float) 
	
	--- ceq HexFloatConstant(SigWhole:Nat, SigFrac:NzNat, Exp:Int) 
		--- = DecimalFloatConstant(Rat2Float((SigWhole:Nat +Rat (1 /Rat SigFrac:NzNat)) *Rat (2 ^Rat Exp:Int)))
		--- if SigFrac:NzNat =/=Bool 0 
		
	--- ceq HexFloatConstant(SigWhole:Nat, SigFrac:Nat, Exp:Int) = DecimalFloatConstant(Rat2Float(SigWhole:Nat *Rat (2 ^Rat Exp:Int)))
		--- if SigFrac:Nat ==Bool 0 
	
	---C99 6.4.4.2:4 An unsuffixed floating constant has type double. If suffixed by the letter f or F, it has type float. If suffixed by the letter l or L, it has type long double
	---FIXME
	--- rule NoSuffix(DecimalFloatConstant(F:Float)) => tv(F:Float, double)
		--- [structural] 
	--- rule L(DecimalFloatConstant(F:Float)) => tv(F:Float, long-double)
		--- [structural] 
	--- rule F(DecimalFloatConstant(F:Float)) => tv(F:Float, float)
		--- [structural] 

endkm

kmod COMMON-SEMANTICS-ASSIGNMENT is
	including COMMON-SEMANTICS-EXPRESSIONS-INCLUDE 
	
	context assign(*([HOLE]), ?) 
	context assign(?, [HOLE]) 
	
	rule [for-assignment]: < k > E1:Expression := E2:Expression => assign(*(&(E1:Expression)),  E2:Expression) ...</ k > 
		[structural] 
	
	--- 6.5.16
	op compoundAssignment : KLabel K K -> K [metadata "strict(2 3)"] 
	rule
		< k > L:KLabel(E1:Expression,, E2:Expression) 
			=> compoundAssignment(L:KLabel, &(E1:Expression), E2:Expression) 
		...</ k >
		if Set(
			l('_*=_),, l('_/=_),, l('_%=_),, l('_+=_),, l('_-=_),, 
			l('_<<=_),, l('_>>=_),, l('_&=_),, l('_^=_),, l('_|=_)
		) contains l(L:KLabel)
		[structural] 

	op getInnerOperator : KLabel -> KLabel 
	rule
		< k > compoundAssignment(L:KLabel, V:Value, V':Value) 
			=> *(V:Value) := getInnerOperator(L:KLabel)(*(V:Value),, V':Value) 
		...</ k >
		[structural] 

	eq getInnerOperator('_*=_) = '_*_ 
	eq getInnerOperator('_/=_) = '_/_ 
	eq getInnerOperator('_%=_) = '_%_ 
	eq getInnerOperator('_+=_) = '_+_ 
	eq getInnerOperator('_-=_) = '_-_ 
	
	eq getInnerOperator('_<<=_) = '_<<_ 
	eq getInnerOperator('_>>=_) = '_>>_ 
	eq getInnerOperator('_&=_) = '_&_ 
	eq getInnerOperator('_^=_) = '_^_ 
	eq getInnerOperator('_|=_) = '_|_ 

	rule [assign]:
		< k > assign(*(tv(Loc:Nat, pointerType(T:Type))), tv(V:List{K}, T':Type)) 
			=> write(Loc:Nat, tv(V:List{K}, T:Type))
			~> tv(V:List{K}, T':Type)
		...</ k >
		if unqualifyType(T:Type) ==Bool T':Type
		[structural] 
	--- C99 6.5.16.1:2 In simple assignment (=), the value of the right operand is converted to the type of the assignment expression and replaces the value stored in the object designated by the left operand
	rule
		< k > assign(*(tv(Loc:Nat, pointerType(T:Type))), (tv(V:List{K}, T':Type) 
			=> cast(unqualifyType(T:Type), tv(V:List{K}, T':Type))))
		...</ k >
		if unqualifyType(T:Type) =/=Bool T':Type
		andBool notBool hasArrayType(T:Type)
		[structural] 
	--- rule
		--- < k > assign(*(tv(Loc:Nat, pointerType((arrayType(T:Type, ?) => pointerType(T:Type))))), ?)
		--- ...</ k >
		--- [structural] 
endkm

kmod COMMON-SEMANTICS-BITWISE is
	including COMMON-SEMANTICS-EXPRESSIONS-INCLUDE 
	
	--- c99 6.5.7:3 The integer promotions are performed on each of the operands. The type of the result is that of the promoted left operand. If the value of the right operand is negative or is greater than or equal to the width of the promoted left operand, the behavior is undefined
	rule tv(I:Int, T:Type) << tv(N:Nat, T':Type) => leftShiftInterpret(T:Type, I:Int <<Int N:Nat, tv(I:Int, T:Type))
		if hasIntegerType(T:Type)
		andBool hasBeenPromoted(T:Type)
		andBool hasBeenPromoted(T':Type)
		andBool hasIntegerType(T':Type)
		andBool N:Nat <Int numBits(T:Type)
		[structural] 
	rule tv(I:Int, T:Type) >> tv(N:Nat, T':Type) => rightShiftInterpret(T:Type, I:Int >>Int N:Nat) 
		if hasIntegerType(T:Type)
		andBool hasBeenPromoted(T:Type)
		andBool hasBeenPromoted(T':Type)
		andBool hasIntegerType(T':Type)
		andBool N:Nat <Int numBits(T:Type)
		[structural] 
				
	rule tv(I1:Int, T:Type) | tv(I2:Int, T:Type) => arithInterpret(T:Type, I1:Int |Int I2:Int)
		if hasIntegerType(T:Type)
		andBool hasBeenPromoted(T:Type)
		[structural] 
	rule tv(I1:Int, T:Type) & tv(I2:Int, T:Type) => arithInterpret(T:Type, I1:Int &Int I2:Int) 
		if hasIntegerType(T:Type)
		andBool hasBeenPromoted(T:Type)
		[structural] 
	rule ~ tv(I:Int, T:Type) => arithInterpret(T:Type, ~Int I:Int)
		if hasIntegerType(T:Type)
		andBool hasBeenPromoted(T:Type)
		[structural] 
	rule tv(I1:Int, T:Type) ^ tv(I2:Int, T:Type) => arithInterpret(T:Type, I1:Int xorInt I2:Int) 
		if hasIntegerType(T:Type)
		andBool hasBeenPromoted(T:Type)
		[structural] 
endkm

kmod COMMON-SEMANTICS-BOOLEAN-ARITHMETIC is
	including COMMON-SEMANTICS-EXPRESSIONS-INCLUDE 
	
	---- comparison of integers
	--- FIXME should also be promoting these
	rule tv(I1:Int, T:Type) < tv(I2:Int, T:Type) 
		=> if (I1:Int <Int I2:Int) then tv(1, int) else tv(0, int) fi 
		if (hasIntegerType(T:Type) andBool hasBeenPromoted(T:Type))
		orBool (hasPointerType(T:Type) andBool isConcreteNumber(I1:Int) andBool isConcreteNumber(I2:Int))
		[structural] 
	rule tv(I1:Int, T:Type) <= tv(I2:Int, T:Type) 
		=> if (I1:Int <=Int I2:Int) then tv(1, int) else tv(0, int) fi
		if (hasIntegerType(T:Type) andBool hasBeenPromoted(T:Type))
		orBool (hasPointerType(T:Type) andBool isConcreteNumber(I1:Int) andBool isConcreteNumber(I2:Int))
		[structural] 
	rule tv(I1:Int, T:Type) > tv(I2:Int, T:Type) 
		=> if (I1:Int >Int I2:Int) then tv(1, int) else tv(0, int) fi
		if (hasIntegerType(T:Type) andBool hasBeenPromoted(T:Type))
		orBool (hasPointerType(T:Type) andBool isConcreteNumber(I1:Int) andBool isConcreteNumber(I2:Int))
		[structural] 
	rule tv(I1:Int, T:Type) >= tv(I2:Int, T:Type) 
		=> if (I1:Int >=Int I2:Int) then tv(1, int) else tv(0, int) fi
		if (hasIntegerType(T:Type) andBool hasBeenPromoted(T:Type))
		orBool (hasPointerType(T:Type) andBool isConcreteNumber(I1:Int) andBool isConcreteNumber(I2:Int))
		[structural] 
		
	rule tv(I1:Int, T:Type) == tv(I2:Int, T:Type) 
		=> if (I1:Int ==Bool I2:Int) then tv(1, int) else tv(0, int) fi
		if (
			(hasIntegerType(T:Type) andBool hasBeenPromoted(T:Type))
			orBool (hasPointerType(T:Type) andBool isConcreteNumber(I1:Int) andBool isConcreteNumber(I2:Int))
		) andBool notBool (isUnknown(I1:Int) orBool isUnknown(I2:Int))
		[structural] 
	rule tv(I1:Int, T:Type) != tv(I2:Int, T:Type) 
		=> if (I1:Int =/=Bool I2:Int) then tv(1, int) else tv(0, int) fi
		if (
			(hasIntegerType(T:Type) andBool hasBeenPromoted(T:Type))
			orBool (hasPointerType(T:Type) andBool isConcreteNumber(I1:Int) andBool isConcreteNumber(I2:Int))
		) andBool notBool (isUnknown(I1:Int) orBool isUnknown(I2:Int))
		[structural] 
		
	op isUnknown : K -> Bool 
	eq isUnknown(piece(?, ?)) = true 
	eq isUnknown(sym(?) +Nat ?) = false 
	eq isUnknown(bito(?) +Nat ?) = false 
	ceq isUnknown(I:Int) = false
		if  I:Int <=Int 0 orBool I:Int >Int 0 
	
	---- comparison of pointers
	--- fixme could check 6.5.8:2
	--- fixme there are further restrictions on pointers
	rule tv(sym(Base:Nat) +Nat N:Nat, T:Type) < tv(sym(Base:Nat) +Nat M:Nat, T':Type) 
		=> if (N:Nat <Int M:Nat) then tv(1, int) else tv(0, int) fi 
	if hasPointerType(T:Type) andBool hasPointerType(T':Type)
	[structural] 
	rule tv(sym(Base:Nat) +Nat N:Nat, T:Type) <= tv(sym(Base:Nat) +Nat M:Nat, T':Type) 
		=> if (N:Nat <=Int M:Nat) then tv(1, int) else tv(0, int) fi 
	if hasPointerType(T:Type) andBool hasPointerType(T':Type)
	[structural] 
	rule tv(sym(Base:Nat) +Nat N:Nat, T:Type) > tv(sym(Base:Nat) +Nat M:Nat, T':Type) 
		=> if (N:Nat >Int M:Nat) then tv(1, int) else tv(0, int) fi 
	if hasPointerType(T:Type) andBool hasPointerType(T':Type)
	[structural] 
	rule tv(sym(Base:Nat) +Nat N:Nat, T:Type) >= tv(sym(Base:Nat) +Nat M:Nat, T':Type) 
		=> if (N:Nat >=Int M:Nat) then tv(1, int) else tv(0, int) fi 
	if hasPointerType(T:Type) andBool hasPointerType(T':Type)
	[structural] 
	
	rule tv(N:Nat, T:Type) == tv(M:Nat, T':Type)
		=> if (N:Nat ==Bool M:Nat) then tv(1, int) else tv(0, int) fi 
		if hasPointerType(T:Type) andBool hasPointerType(T':Type)
		[structural] 
	rule tv(N:Nat, T:Type) != tv(M:Nat, T':Type) 
		=> if (N:Nat =/=Bool M:Nat) then tv(1, int) else tv(0, int) fi
		if hasPointerType(T:Type) andBool hasPointerType(T':Type)
		[structural] 
		
	---- comparison of ints with pointers
	--- fixme there are further restrictions on pointers
	rule (tv(N:Nat, T:Type) => tv(NullPointer, T':Type)) == tv(?, T':Type)
		if hasIntegerType(T:Type) andBool hasPointerType(T':Type)
		andBool hasBeenPromoted(T:Type)
		andBool N:Nat ==Bool NullPointerConstant
		[structural] 
	rule tv(?, T:Type) == (tv(N:Nat, T':Type) => tv(NullPointer, T:Type))
		if hasPointerType(T:Type) andBool hasIntegerType(T':Type)
		andBool hasBeenPromoted(T':Type)
		andBool N:Nat ==Bool NullPointerConstant
		[structural] 
	
	rule (tv(N:Nat, T:Type) => tv(NullPointer, T':Type)) != tv(?, T':Type)
		if hasIntegerType(T:Type) andBool hasPointerType(T':Type)
		andBool hasBeenPromoted(T:Type)
		andBool N:Nat ==Bool NullPointerConstant
		[structural] 
	rule tv(?, T:Type) != (tv(N:Nat, T':Type) => tv(NullPointer, T:Type))
		if hasPointerType(T:Type) andBool hasIntegerType(T':Type)
		andBool hasBeenPromoted(T':Type)
		andBool N:Nat ==Bool NullPointerConstant
		[structural]

	--- floats
	rule 
		tv(F1:Float, T:Type) < tv(F2:Float, T:Type) => if (F1:Float <Float F2:Float) then tv(1, int) else tv(0, int) fi
		[structural] 
	rule 
		tv(F1:Float, T:Type) <= tv(F2:Float, T:Type) => if (F1:Float <=Float F2:Float) then tv(1, int) else tv(0, int) fi 
		[structural] 
	rule 
		tv(F1:Float, T:Type) > tv(F2:Float, T:Type) => if (F1:Float >Float F2:Float) then tv(1, int) else tv(0, int) fi
		[structural] 
	rule 
		tv(F1:Float, T:Type) >= tv(F2:Float, T:Type) => if (F1:Float >=Float F2:Float) then tv(1, int) else tv(0, int) fi
		[structural] 
	rule 
		tv(F1:Float, T:Type) == tv(F2:Float, T:Type) => if (F1:Float ==Bool F2:Float) then tv(1, int) else tv(0, int) fi
		[structural] 
	rule 
		tv(F1:Float, T:Type) != tv(F2:Float, T:Type) => if (F1:Float =/=Bool F2:Float) then tv(1, int) else tv(0, int) fi
		[structural] 
endkm

kmod COMMON-SEMANTICS-ARITHMETIC is
	including COMMON-SEMANTICS-EXPRESSIONS-INCLUDE 
		
	--- FIXME needs to check offset > 0 
	rule < k > tv(Loc:Nat, pointerType(T':Type)) + tv(I2:Int, T:Type)
				=> cast(pointerType(T':Type), cast(pointerType(unsigned-char), tv(Loc:Nat, pointerType(T':Type))) + (tv(I2:Int, T:Type) * sizeofType(T':Type)))
		...</ k >
		if hasIntegerType(T:Type)
		andBool T':Type =/=Bool void
		andBool T':Type =/=Bool unsigned-char
		[structural] 
	--- same as above, but swap arguments
	rule < k > tv(I2:Int, T:Type) + tv(Loc:Nat, pointerType(T':Type))
				=> cast(pointerType(T':Type), cast(pointerType(unsigned-char), tv(Loc:Nat, pointerType(T':Type))) + (tv(I2:Int, T:Type) * sizeofType(T':Type)))
		...</ k >
		if hasIntegerType(T:Type)
		andBool T':Type =/=Bool void
		andBool T':Type =/=Bool unsigned-char
		[structural] 
		
	rule < k > tv(Loc:Nat, pointerType(unsigned-char)) + tv(I2:Int, T:Type) 
			=> tv(Loc:Nat +Int I2:Int, pointerType(unsigned-char))
		...</ k >
		if hasIntegerType(T:Type)
		[structural] 
		
	rule < k > tv(Loc:Nat, pointerType(T':Type)) - tv(I2:Int, T:Type)
				=> cast(pointerType(T':Type), cast(pointerType(unsigned-char), tv(Loc:Nat, pointerType(T':Type))) - (tv(I2:Int, T:Type) * sizeofType(T':Type)))
		...</ k >
		if hasIntegerType(T:Type)
		andBool T':Type =/=Bool void
		andBool T':Type =/=Bool unsigned-char
		[structural] 
		
	rule < k > tv(Loc:Nat, pointerType(unsigned-char)) - tv(I2:Int, T:Type) 
			=> tv(Loc:Nat -Int I2:Int, pointerType(unsigned-char))
		...</ k >
		if hasIntegerType(T:Type)
		[structural]
		
	op computePointerDifference : Int Int K -> K [metadata "strict(3)"] --- ptr1, ptr2, size of ptr type
	rule [start-pointer-difference]: tv(I1:Int, pointerType(T:Type)) - tv(I2:Int, pointerType(T:Type)) 
		=> computePointerDifference(I1:Int, I2:Int, sizeofType(T:Type))
		[structural] 
	rule [pointer-difference]: computePointerDifference(sym(Block:Nat) +Nat Offset1:Nat, sym(Block:Nat) +Nat Offset2:Nat, tv(Size:Nat, ?))
		=> tv(_-Int_(Offset1:Nat, Offset2:Nat) /Int Size:Nat, cfg:ptrdiffut)
		if _-Int_(Offset1:Nat, Offset2:Nat) %Int Size:Nat ==Bool 0
		[structural]
		
	rule - tv(I:Int, T:Type) => arithInterpret(T:Type, (-Int I:Int))
		if hasIntegerType(T:Type) 
		andBool rank(T:Type) >=Int rank(int)
		andBool hasBeenPromoted(T:Type)
		[structural] 
		
	rule + tv(I:Int, T:Type) => arithInterpret(T:Type, I:Int)
		if hasIntegerType(T:Type)
		andBool rank(T:Type) >=Int rank(int)
		andBool hasBeenPromoted(T:Type)
		[structural] 
		
	rule tv(I1:Int, T:Type) + tv(I2:Int, T:Type) => arithInterpret(T:Type, (I1:Int +Int I2:Int))
		if hasIntegerType(T:Type) 
		andBool rank(T:Type) >=Int rank(int)
		andBool hasBeenPromoted(T:Type)
		[structural] 
	rule _-_(tv(I1:Int, T:Type), tv(I2:Int, T:Type)) => arithInterpret(T:Type, _-Int_(I1:Int,I2:Int))
		if hasIntegerType(T:Type) 
		andBool rank(T:Type) >=Int rank(int)
		andBool hasBeenPromoted(T:Type)
		[structural] 
	rule tv(I1:Int, T:Type) * tv(I2:Int, T:Type) => arithInterpret(T:Type, I1:Int *Int I2:Int)
		if hasIntegerType(T:Type) 
		andBool rank(T:Type) >=Int rank(int)
		andBool hasBeenPromoted(T:Type)
		[structural] 
	rule tv(I1:Int, T:Type) / tv(I2:Int, T:Type) => arithInterpret(T:Type, I1:Int /Int I2:Int) 
		if hasIntegerType(T:Type) 
		andBool rank(T:Type) >=Int rank(int)
		andBool hasBeenPromoted(T:Type)
		andBool I2:Int =/=Bool 0
		[structural] 
	rule tv(I1:Int, T:Type) % tv(I2:Int, T:Type) => arithInterpret(T:Type, I1:Int %Int I2:Int) 
		if hasIntegerType(T:Type) 
		andBool rank(T:Type) >=Int rank(int)
		andBool hasBeenPromoted(T:Type)
		andBool I2:Int =/=Bool 0
		[structural] 
	rule - tv(I1:Int, T:Type) => arithInterpret(T:Type, -Int_(I1:Int))
		if hasIntegerType(T:Type) 
		andBool rank(T:Type) >=Int rank(int)
		andBool hasBeenPromoted(T:Type)
		[structural] 
	
	--- floats
	--- fixme
	rule tv(F1:Float, T:Type) + tv(F2:Float, T:Type) => arithInterpret(T:Type, F1:Float +Float F2:Float)
		[structural] 
	rule _-_(tv(F1:Float, T:Type), tv(F2:Float, T:Type)) => arithInterpret(T:Type, _-Float_(F1:Float, F2:Float))
		[structural] 
	rule tv(F1:Float, T:Type) * tv(F2:Float, T:Type) => arithInterpret(T:Type, F1:Float *Float F2:Float)
		[structural] 
	rule tv(F1:Float, T:Type) / tv(F2:Float, T:Type) => arithInterpret(T:Type, F1:Float /Float F2:Float)
		[structural] 
	rule - tv(F:Float, T:Type) => arithInterpret(T:Type, -Float_(F:Float))
		[structural] 
	rule + tv(F:Float, T:Type) => tv(F:Float, T:Type)
		[structural] 
endkm

kmod COMMON-SEMANTICS-MEMBERS is 
	including COMMON-SEMANTICS-EXPRESSIONS-INCLUDE 
	
	rule [arrow-struct]:
		< k > tv(Base:Int, pointerType(T:Type)) -> F:Id 
			=> *(tv(Base:Int, pointerType(T:Type))) . F:Id 
		...</ k >
		if hasStructType(T:Type)
		orBool hasUnionType(T:Type)
		[structural] 

	op toEval : K -> K 
	op toEval-aux : K K -> K [metadata "strict(2)"] 
	
	rule [dot]:
		< k > K:K . F:Id => toEval(K:K . F:Id) ...</ k >
		[structural] 
	rule
		< k > toEval(K:K) => toEval-aux(K:K, typeof(K:K))  ...</ k >
		[structural] 
		
	rule
		< k > toEval-aux(K:K, arrayType(T:Type, N:Nat)) => &(K:K) ...</ k >
		[structural] 
	--- rule
		--- < k > toEval-aux(K:K, arrayType(T:Type, N:Nat)) => cast(arrayType(T:Type, N:Nat), &(K:K)) ...</ k >
		--- [structural] 
	op toEval-value : K -> K 
	context toEval-value(`[HOLE`]:K . ?) 
	rule
		< k > toEval-aux(K:K, T:Type) => toEval-value(K:K) ...</ k >
		if notBool hasArrayType(T:Type)
		[structural]
	rule
		< k > toEval-value(tv(L:List{K}, T:Type) . F:Id)
			=> extractField(L:List{K}, T:Type, F:Id) 
		...</ k >
		[structural]

					
	---C99 6.5.2.3:4 86) If &E is a valid pointer expression (where & is the "address-of" operator, which generates a pointer to its operand), the expression (&E)->MOS is the same as E.MOS
		
  	---C99 6.5.2.3:4 86) If &E is a valid pointer expression (where & is the "address-of" operator, which generates a pointer to its operand), the expression (&E)->MOS is the same as E.MOS
endkm

kmod COMMON-SEMANTICS-DEREFERENCE is
	including COMMON-SEMANTICS-EXPRESSIONS-INCLUDE 
	
	---C99 6.5.3.2:4 The unary * operator denotes indirection. If the operand points to a function, the result is a function designator; if it points to an object, the result is an lvalue designating the object. If the operand has type "pointer to type", the result has type "type". If an invalid value has been assigned to the pointer, the behavior of the unary * operator is undefined
	---xxx also see 6.3.2.1:3 for why i made the result a pointerType
	---- fixme this seems wrong
	rule < k > *(tv(Loc:Nat, pointerType(arrayType(T:Type, N:Nat)))) 
			=> tv(Loc:Nat, arrayType(T:Type, N:Nat)) 
		...</ k > 
		[structural] 
	rule < k > *(tv(Loc:Nat, pointerType(incompleteArrayType(T:Type)))) 
			=> tv(Loc:Nat, incompleteArrayType(T:Type)) 
		...</ k > 
		[structural] 
		
	
	--- fixme these are both pretty fishy
	--- rule < k > *(tv(Loc:Nat, pointerType(arrayType(T:Type, N:Nat)))) 
		--- => tv(Loc:Nat, arrayType(T:Type, N:Nat)) 
	--- ...</ k > [structural] 
	rule < k > *(tv(Loc:Nat, pointerType(functionType(T:Type, L:List{Type})))) 
		=> tv(Loc:Nat, pointerType(functionType(T:Type, L:List{Type}))) 
	...</ k > [structural] 
	
	--- FIXME this rule is super dangerous because if the value ends up inside any helper operator, it will match
	--- rule KL:KLabel((?,, tv(?, (arrayType(T:Type, ?) => pointerType(T:Type))),, ?))
		--- if KL:KLabel =/=Bool 'SizeofExpression
		--- andBool KL:KLabel =/=Bool 'SizeofType
		--- andBool KL:KLabel =/=Bool '&_
		--- 
		
	--- matching the sym in order to catch instances of dereferencing a non-pointer
	rule [deref]:
		< k > *(tv(sym(Block:Nat) +Nat Offset:Nat, pointerType(T:Type))) 
			=> read(sym(Block:Nat) +Nat Offset:Nat, T:Type)
		...</ k >
		if notBool hasArrayType(T:Type)
		andBool notBool hasFunctionType(T:Type)
		[structural] 
endkm

kmod COMMON-SEMANTICS-REFERENCE is
	including COMMON-SEMANTICS-EXPRESSIONS-INCLUDE 
	
	context &([HOLE] -> X:Id) 
	
	op fixPointerType : Type -> Type 
	ceq fixPointerType(T:Type) = pointerType(T:Type)
		if notBool(hasArrayType(T:Type)) 
	eq fixPointerType(arrayType(T:Type, ?)) = pointerType(T:Type) 
	
	--- C1X 6.5.3.2:3 The unary & operator yields the address of its operand. If the operand has type ‘‘type’’, the result has type ‘‘pointer to type’’. If the operand is the result of a unary * operator, neither that operator nor the & operator is evaluated and the result is as if both were omitted, except that the constraints on the operators still apply and the result is not an lvalue. Similarly, if the operand is the result of a [] operator, neither the & operator nor the unary * that is implied by the [] is evaluated and the result is as if the & operator were removed and the [] operator were changed to a + operator. Otherwise, the result is a pointer to the object or function designated by its operand
	
	rule &(*(E:Expression)) => E:Expression 
		[structural] 
	rule &(E1:Expression[E2:Expression]) => E1:Expression + E2:Expression 
		[structural] 
	rule [ref]:
		< k > &(X:Id) => tv(Loc:Nat, pointerType(T:Type)) ...</ k >
		< env >... X:Id |-> Loc:Nat ...</ env >
		< types >... X:Id |-> T:Type ...</ types >
		[structural] 
	
	op getOffset : K K Type -> K 
	
	context getOffset(?, value(`[HOLE`]:K), ?) 
	rule [address-of-arrow-struct]:
		< k > &(tv(Loc:Nat, pointerType(structType(S:Id))) -> X:Id)
			=> getOffset(Loc:Nat, value(calculateLength(L1:List{Type})), fixPointerType(T:Type))
		...</ k >
		< structs >... S:Id |-> (L1:List{Type} :: typedDeclaration(T:Type, X:Id) :: ?) ...</ structs >
		[structural] 
	rule [address-of-arrow-union]:
		< k > &(tv(Loc:Nat, pointerType(unionType(S:Id))) -> X:Id)
			=> getOffset(Loc:Nat, 0, fixPointerType(T:Type))
		...</ k >
		< structs >... S:Id |-> (? :: typedDeclaration(T:Type, X:Id) :: ?) ...</ structs >
		[structural] 
		
	eq getOffset(N:Nat, M:Nat, T:Type) = tv(N:Nat +Nat bito(M:Nat), T:Type) 
		
	rule [address-of-dot]:
		< k > &(E:Expression . X:Id) => &(&(E:Expression) -> X:Id) ...</ k >
		[structural] 
		
	--- fixme is there any more general way to do this?  it seems awful awkward
	rule [address-of-compound]:
		< k > & CompoundLiteral(N:Nat, Spec:K, Decl:K, Init:K) 
			=> Computation(CompoundLiteral(N:Nat, Spec:K, Decl:K, Init:K))
			~> & compoundLiteral(N:Nat)
		...</ k >
		[structural] 
endkm

kmod COMMON-SEMANTICS-INCREMENT-AND-DECREMENT is
	including COMMON-SEMANTICS-EXPRESSIONS-INCLUDE 
	
	--- c1x 6.5.3.1:2 The value of the operand of the prefix ++ operator is incremented. The result is the new value of the operand after incrementation. The expression ++E is equivalent to (E+=1). See the discussions of additive operators and compound assignment for information on constraints, types, side effects, and conversions and the effects of operations on pointers
	eq ++ E:Expression = E:Expression += tv(1, int) 
	--- c1x 6.5.3.1:3 The prefix -- operator is analogous to the prefix ++ operator, except that the value of the operand is decremented
	eq -- E:Expression = E:Expression -= tv(1, int) 

	op postOpRef : K KLabel -> K 
	context postOpRef(*([HOLE]), ?) 

	rule [make-postinc-ref]: < k > E:Expression ++ => postOpRef(*(&(E:Expression)), '_++) ...</ k > 
		[structural] 
	rule [make-postdec-ref]: < k > E:Expression -- => postOpRef(*(&(E:Expression)), '_--) ...</ k > 
		[structural] 

	op postInc : K K Type -> K [metadata "strict(2)"] 
	op postDec : K K Type -> K [metadata "strict(2)"] 

	rule [post-increment-start]:
		< k > postOpRef(*(tv(Loc:Nat, pointerType(T:Type))), '_++)
			=> postInc(Loc:Nat, read(Loc:Nat, T:Type), T:Type)
		...</ k >
		[structural] 
	rule [post-decrement-start]:
		< k > postOpRef(*(tv(Loc:Nat, pointerType(T:Type))), '_--)
			=> postDec(Loc:Nat, read(Loc:Nat, T:Type), T:Type)
		...</ k >
		[structural] 

	rule [post-increment]:
		< k > postInc(Loc:Nat, tv(V:BaseValue, T:Type), T:Type)
			=> *(tv(Loc:Nat, pointerType(T:Type))) := tv(V:BaseValue, T:Type) + tv(1, int)
			~> discard
			~> tv(V:BaseValue, T:Type)
		...</ k >
		[structural] 
		
	rule [post-decrement]:
		< k > postDec(Loc:Nat, tv(V:BaseValue, T:Type), T:Type)
			=> *(tv(Loc:Nat, pointerType(T:Type))) := tv(V:BaseValue, T:Type) - tv(1, int)
			~> discard
			~> tv(V:BaseValue, T:Type)
		...</ k >
		[structural] 
endkm

kmod COMMON-SEMANTICS-SEQUENCING is
	including COMMON-SEMANTICS-EXPRESSIONS-INCLUDE 
	
	rule < k > Comma(K:C :: K':C :: L:List{C}) => Computation(K:C) ~> Comma(K':C :: L:List{C}) ...</ k >
		[structural] 
	rule < k > Comma(K:C) => K:C ...</ k >
		[structural] 
endkm

kmod COMMON-C-EXPRESSIONS is
	including COMMON-SEMANTICS-EXPRESSIONS-INCLUDE 

	including COMMON-SEMANTICS-ABSTRACTION 
	including COMMON-SEMANTICS-COMPOUND-LITERAL 
	including COMMON-SEMANTICS-BOOLEAN 
	including COMMON-SEMANTICS-SIZEOF 
	including COMMON-SEMANTICS-IDENTIFIERS 
	including COMMON-SEMANTICS-FUNCTION-CALLS 
	including COMMON-SEMANTICS-ARRAY-SUBSCRIPTING 
	including COMMON-SEMANTICS-ASSIGNMENT 
	including COMMON-SEMANTICS-LITERALS 
	including COMMON-SEMANTICS-BITWISE 
	including COMMON-SEMANTICS-BOOLEAN-ARITHMETIC 
	including COMMON-SEMANTICS-ARITHMETIC 
	including COMMON-SEMANTICS-MEMBERS 
	including COMMON-SEMANTICS-DEREFERENCE 
	including COMMON-SEMANTICS-REFERENCE 
	including COMMON-SEMANTICS-INCREMENT-AND-DECREMENT 
	including COMMON-SEMANTICS-SEQUENCING 
	
	eq NothingExpression = emptyValue 
endkm
