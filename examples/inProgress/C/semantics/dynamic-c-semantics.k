kmod DYNAMIC-C-SEMANTICS is
	including COMMON-C-SEMANTICS
	
---C99 5.1.2.2.1:2
--- If they are declared, the parameters to the main function shall obey the following
--- constraints:
--- — The value of argc shall be nonnegative.
--- — argv[argc] shall be a null pointer.
--- — If the value of argc is greater than zero, the array members argv[0] through
--- argv[argc-1] inclusive shall contain pointers to strings, which are given
--- implementation-defined values by the host environment prior to program startup. The
--- intent is to supply to the program information determined prior to program startup
--- from elsewhere in the hosted environment. If the host environment is not capable of
--- supplying strings with letters in both uppercase and lowercase, the implementation
--- shall ensure that the strings are received in lowercase.
--- — If the value of argc is greater than zero, the string pointed to by argv[0]
--- represents the program name; argv[0][0] shall be the null character if the
--- program name is not available from the host environment. If the value of argc is
--- greater than one, the strings pointed to by argv[1] through argv[argc-1]
--- represent the program parameters.
--- — The parameters argc and argv and the strings pointed to by the argv array shall
--- be modifiable by the program, and retain their last-stored values between program
--- startup and program termination.	
	--- op #incomingArgumentArray : -> Id [ctor]
	op incomingArguments : List{K} -> K
	op incomingArguments-aux : List{K} Nat -> K
	
	eq incomingArguments(L:List{K}) = incomingArguments-aux(L:List{K}, 0)
	eq incomingArguments-aux((S:String,, L:List{K}), N:Nat) 
		= (Identifier("#incomingArgumentsArray")[N:Nat] := StringLiteral(S:String))
			~> discard
			~> incomingArguments-aux(L:List{K}, sNat(N:Nat))
	eq incomingArguments-aux(.List{K}, N:Nat) 
		= (Identifier("#incomingArgumentsArray")[N:Nat] := NullPointer)
			~> discard

---C99 5.1.2.2.1:1
--- The function called at program startup is named main. The implementation declares no
--- prototype for this function. It shall be defined with a return type of int and with no
--- parameters:
--- int main(void) { /* ... */ }
--- or with two parameters (referred to here as argc and argv, though any names may be
--- used, as they are local to the function in which they are declared):
--- int main(int argc, char *argv[]) { /* ... */ }
--- or equivalent;9) or in some other implementation-defined manner

	--- op unclutterConfiguration : Bag -> Bag
	--- op stripConfiguration : Bag -> Bag
	
	--- doesn't [owise] rules :(
	---eq unclutterConfiguration(B:Bag) = stripConfiguration(B:Bag) [owise] .
	
	--- eq stripConfiguration(B0:Bag (< T > B1:Bag (< aLabelMap > M:Map </ aLabelMap >) </ T >)) = stripConfiguration(B0:Bag < T > B1:Bag </ T >) .
	--- eq stripConfiguration(B0:Bag (< T > B1:Bag
		--- < threads > B2:Bag
				--- < thread > B3:Bag
					--- < callStack > ?:List </ callStack >
				--- </ thread >
		--- </ threads >
	--- </ T >)) = stripConfiguration(B0:Bag < T > B1:Bag 
		--- < threads > B2:Bag
			--- < thread > B3:Bag
			--- </ thread >
		--- </ threads > </ T >) .
	--- eq stripConfiguration(B0:Bag (< T > B1:Bag
		--- < threads > B2:Bag
				--- < thread > B3:Bag
					--- < types > ?:Map </ types >
				--- </ thread >
		--- </ threads >
	--- </ T >)) = stripConfiguration(B0:Bag < T > B1:Bag 
		--- < threads > B2:Bag
			--- < thread > B3:Bag
			--- </ thread >
		--- </ threads > </ T >) .
	--- eq stripConfiguration(B0:Bag (< T > B1:Bag
		--- < mem > M:Map
			--- B:Nat |-> memblock(N:Nat, (0 |-> Closure(X:Id, functionType(?, ?), ?)))
		--- </ mem >
	--- </ T >)) = stripConfiguration(B0:Bag < T > B1:Bag 
		--- < mem > M:Map
			--- B:Nat |-> memblock(N:Nat, (0 |-> Closure(X:Id, .K, .K)))
		--- </ mem >
		--- </ T >) .
	--- eq stripConfiguration(B0:Bag (< T > B1:Bag
		--- < typedefs > ?:Map </ typedefs >
	--- </ T >)) = stripConfiguration(B0:Bag < T > B1:Bag </ T >) .
	--- eq stripConfiguration(B0:Bag (< T > B1:Bag
		--- < genv > ?:Map </ genv >
	--- </ T >)) = stripConfiguration(B0:Bag < T > B1:Bag </ T >) .

	--- this bit of indirection is used to check that the main prototype is correct, and to call it with the appropriate arguments
	op callMain : Nat Id -> K
	op callMain-aux : K Nat Id -> K [strict(1)]
	
	rule < k > callMain(N:Nat, X:Id) 
		=> callMain-aux(typeof(Identifier("main")), N:Nat, X:Id)
	...</ k >
	< functionTranslationUnits >... Tu:K |-> Map((? Identifier("main") |-> Tu:K)) ...</ functionTranslationUnits >
	< currentTranslationUnit > ? => Tu:K </ currentTranslationUnit >
	
	--- FIXME i think these are slightly different
	--- fixme void isn't supposed to have a name
	--- fixme figure out type of string
	eq callMain-aux(functionType(int, typedDeclaration(void, ?)), N:Nat, X:Id) = Call(Identifier("main"), Nil)
	eq callMain-aux(functionType(int, Nil), N:Nat, X:Id) = Call(Identifier("main"), Nil)
	eq callMain-aux(functionType(int, (typedDeclaration(int, ?) :: typedDeclaration(incompleteArrayType(pointerType(signed-char)), ?))), N:Nat, X:Id)
		= Call(Identifier("main"), N:Nat :: X:Id)
		
***(
('callMain-aux).KProperLabel(('functionType).KResultLabel(BaseType int(.List{K}),,('_::_).KHybridLabel(('typedDeclaration).KResultLabel(BaseType int(.List{K}),,Id Identifier("argc")(.List{K})),,('typedDeclaration).KResultLabel(('incompleteArrayType).KResultLabel(('pointerType).KResultLabel(BaseType signed-char(.List{K}))),,Id Identifier("argv")(.List{K})))),,BaseValue 1(.List{K}),,Id Identifier("#incomingArgumentsArray")(.List{K}))
***)
	op syntaxNat : Nat -> K
	eq syntaxNat(N:Nat) = Constant(IntLiteral(NoSuffix(DecimalConstant(N:Nat))))
	
	eq eval(K:K) = eval(K:K, .List{K}, "")
	eq eval(Program(P:List{C}), L:List{K}, Input:String) = 
		< T >
			< threads >
				< thread >
					< control >
						< k > listToK(P:List{C})
							~> DeclarationDefinition(InitNameGroup(Specifier(Char), (InitName(AttributeWrapper(NameLoc(Name(Identifier("#incomingArgumentsArray"), AttributeWrapper(PointerType(AttributeWrapper(ArrayType(JustBase, syntaxNat(sNat(lengthList{K} L:List{K}))), Nil)), Nil)), UnknownCabsLoc), Nil), NoInit))))
							--- ~> (Declaration(char, Pointer(incomingArgumentArray[sNat(length L:List{K})]))) 
							~> resolveReferences							
							~> incomingArguments(L:List{K})
							~> callMain(lengthList{K}(L:List{K}), Identifier("#incomingArgumentsArray"))
						</ k >
							--- Call(Identifier("main"), (Nil
								--- (Constant(IntLiteral(DecimalConstant(length L:List{K})))) 
								--- :: (incomingArgumentArray)
							---xxx )) </ k >
						< currentFunction > File-Scope </ currentFunction >
						< currentProgramLoc > UnknownCabsLoc </ currentProgramLoc >
					...</ control >
				...</ thread >
			</ threads >
			< nextLoc > sym(1) +Nat 0 </ nextLoc >
			< nextFile > 3 </ nextFile >
			< openFiles >
				0 |-> "stdin" --- stdin
				1 |-> "stdout" --- stdout
				2 |-> "stdout" --- stderr
			</ openFiles >
		...</ T >
		< files > 
			"stdin" |-> Input:String
			"stdout" |-> ""
		</ files >
	***(
	--- throw away annotations
	mb [no-annotations]: rule [annotation(?); => .K] : KSentence [metadata "structural"] .
	
	--- fixme I'm not sure threads clean up their memory
	
	--- this shouldn't happen for normal programs (functions end in a return).  it is only used for threads
	mb [terminate-thread]: rule
		[< thread >... < k > .K </ k > ...</ thread > => .Bag]
		: KSentence [metadata "structural"] .
	***)		
	rule [terminate] :
		(< T >... < threads > < thread >... < k > V:Value </ k > ...</ thread > </ threads > ...</ T >
		=> < resultValue > V:Value </ resultValue >)
		< files >...
			"stdin" |-> S1:String	"stdout" |-> S2:String => .Map
		...</ files >
		(.Bag => < input > S1:String </ input >	< output > S2:String </ output >)

endkm
