--- when adding a new builtin library function, don't forget to register it in common-c-semantics in the "builtinIdentifiers" set



------------------------------------------------
---- C standard library
kmod COMMON-C-STANDARD-LIBRARY is
	including COMMON-INCLUDE 
	--- including PL-SOCKET 
	--- including PL-TCP-INTERFACE 
	
	op vararg : K -> Value [strict hybrid] 
	op nextvarg : Nat Type -> C 
	--- fixme had to make this K because of the context bug
	op nextvarg-aux : K Type K -> C --- offset, type, length
	op C : K -> C 
	eq C(K:K) = K:K 
	--- op stupidList : List{C} -> Value 
	--- op makeStupidList : -> K 
	context nextvarg-aux(?, ?, value(`[HOLE`]:K)) 
	--- mb context vararg(value(`[HOLE`]:K)) 
	op debug : -> K 
	op vpair : K K -> C [hybrid strict] 
	rule
		< k > nextvarg(Loc:Nat, T:Type) 
			=> nextvarg-aux(Loc:Nat, T:Type, value(byteSizeofType(T:Type)))
		...</ k >
		[structural] 
	rule
		< k > nextvarg-aux(Loc:Nat, T:Type, Len:Nat)
			=> vpair(read(Loc:Nat, T:Type), vararg(tv(Loc:Nat +Nat Len:Nat, pointerType(unsigned-char))))
		...</ k >
		[structural] 
		
	--- eq L:List{Type} ~> makeStupidList = stupidList(L:List{Type}) 
	--- eq .List{K} :: stupidList(L':List{C}) = L':List{C} 
	
	op prepareBuiltin : Id List{C} -> K [strict(2)] 
	op idsFromDeclList : List{C} -> List{C} 
	
	ceq idsFromDeclList(L:List{C} :: typedDeclaration(T:Type, X:Id)) 
		= idsFromDeclList(L:List{C}) :: X:Id
		if T:Type =/=Bool void 
	eq idsFromDeclList(L:List{C} :: typedDeclaration(void, X:Id)) 
		= idsFromDeclList(L:List{C}) 
	eq idsFromDeclList(L:List{C} :: typedDeclaration(T:Type, X:Id) :: variadic)
		= idsFromDeclList(L:List{C} :: typedDeclaration(T:Type, X:Id)) :: vararg(cast(pointerType(unsigned-char), &(X:Id)) + byteSizeofType(T:Type)) 
	eq idsFromDeclList(Nil) = Nil 
		
	rule
		< k > handleBuiltin(F:Id, functionType(Return:Type, L:List{Type}))
			=> Return(prepareBuiltin(F:Id, idsFromDeclList(L:List{Type})))
		...</ k >
	[structural] 

	--- op builtin : Id -> Value 
	
	--- rule [debug-is-value]:
		--- < k > [debug => builtin(debug)] ...</ k >
	--- [structural] 
	--- rule [debug]:
		--- < k > [prepareBuiltin((debug), ?) => skipval] ...</ k >
	--- [structural] 
	--- --------------------------------------------
	--- rule [setjmp-is-value]:
		--- < k > [setjmp => builtin(setjmp)] ...</ k >
	--- [structural] 
	
	--- --- The (apparent) return value from setjmp indicates whether control reached that point normally or from a call to longjmp
	--- --- fixme check bounds
	--- op Bag : Bag -> K 
	--- rule [setjmp]:
		--- < thread > 
			--- B:Bag
			--- < k > [prepareBuiltin((setjmp), tv(loc(Block:Nat, Offset:Nat), pointerType(structType(?)))) => tv(0, int)] ~> K:K </ k >
		--- </ thread >
		--- < mem >... Block:Nat |-> memblock(?, [M:Map => M:Map[Bag(B:Bag < k > K:K </ k >) / Offset:Nat]]) ...</ mem >
	--- [structural] 
	--- --------------------------------------------
	--- rule [longjmp-is-value]:
		--- < k > [longjmp => builtin(longjmp)] ...</ k >
	--- [structural] 

	--- rule [longjmp]:
		--- < thread >
		--- [?
		--- < k > prepareBuiltin((longjmp), (tv(loc(Block:Nat, Offset:Nat), pointerType(structType(?))):: tv(I:Int, int))) ~> ? </ k >
		--- => B:Bag
		--- < k > tv(if I:Int ==Bool 0 then 1 else I:Int fi, int) ~> K:K </ k >
		--- ]
		--- </ thread >
		--- < mem >... Block:Nat |-> memblock(?, (? Offset:Nat |-> [Bag(B:Bag < k > K:K </ k >) => piece(unknown(Fresh:Nat), 8)])) ...</ mem >
		--- < freshNat > [Fresh:Nat => sNat(Fresh:Nat)] </ freshNat >
	--- [structural] 
	--- --------------------------------------------
	--- rule [spawn-is-value]:
		--- < k > [spawn => builtin(spawn)] ...</ k >
	--- [structural] 
	--- --- had to move < callStack > .List </ callStack > due to spawn
	--- --- Closure(X:Id, functionType(R:Type, P:List{K}), B:K)
	--- rule [spawn]:
		--- < thread > 
			--- C:Bag 
			--- < callStack > ?:List </ callStack >
			--- < k > [prepareBuiltin((spawn), (Fun:Value :: L:List{KResult})) => skipval] ...</ k > 
		--- </ thread >
		--- [.Bag => 
		--- < thread > 
			--- C:Bag
			--- < callStack > .List </ callStack > 
			--- < k > Call(Fun:Value, L:List{KResult}) ~> discard </ k > 
		--- </ thread >]
	--- [structural] 
	--- --------------------------------------------
	--- rule [lock-is-value]:
		--- < k > [lock => builtin(lock)] ...</ k >
	--- [structural] 
	--- rule [lock]:
		--- < k > [prepareBuiltin((lock), tv(Loc:Nat, pointerType(?))) => skipval] ...</ k >
		--- < busy > Busy:Bag [.Bag => BagItem(Loc:Nat)] </ busy >
		--- < holds >... [.Map => Loc:Nat |-> 0] ...</ holds >
		--- if notBool Loc:Nat in Busy:Bag
	--- [metadata "computational rule"] . --- nondet
	--- rule [lock]:
		--- < k > [prepareBuiltin((lock), tv(Loc:Nat, pointerType(?))) => skipval] ...</ k >
		--- < holds >... Loc:Nat |-> [N:Nat => sNat(N:Nat)] ...</ holds >
	--- [metadata "computational rule"] . --- nondet
	--- --------------------------------------------
	--- rule [unlock-is-value]:
		--- < k > [unlock => builtin(unlock)] ...</ k >
	--- [structural] 
	--- rule [unlock]:
		--- < k > [prepareBuiltin((unlock), tv(Loc:Nat, pointerType(?))) => skipval] ...</ k >
		--- < busy >...[BagItem(Loc:Nat) => .Bag] ...</ busy >
		--- < holds >... [Loc:Nat |-> 0 => .Map] ...</ holds >
	--- [structural] 
	--- rule [unlock]:
		--- < k > [prepareBuiltin((unlock), tv(Loc:Nat, pointerType(?))) => skipval] ...</ k >
		--- < holds >... Loc:Nat |-> [sNat(N:Nat) => N:Nat] ...</ holds >
	--- [structural] 
	--- --------------------------------------------
	--- rule [sync-is-value]:
		--- < k > [sync => builtin(sync)] ...</ k >
	--- [structural] 
	--- rule [sync]:
		--- < threads >
			--- < thread >...
				--- < k > [prepareBuiltin((sync), Nil) => skipval] ...</ k > 
			--- ...</ thread >
		--- </ threads >
	--- [structural] 
	--------------------------------------------
	
	
	
	--- rule [exit-is-value]:
		--- < k > Identifier("exit") => builtin(Identifier("exit")) ...</ k >
		--- [structural] 
	rule [exit]:
		< k > prepareBuiltin((Identifier("exit")), tv(I:Int, int)) ~> ? => tv(I:Int, int) </ k >
		[structural] 
	--------------------------------------------
	--- rule [abort-is-debug]:
		--- < k > [abort => debug] ...</ k >
	--- 
	--- rule [abort-is-value]:
		--- < k > Identifier("abort") => builtin(Identifier("abort")) ...</ k >
		--- 
	rule [abort]:
		< k > prepareBuiltin((Identifier("abort")), Nil) ~> ? => tv(134, int) </ k >
		
	--------------------------------------------
	--- rule [sqrt-is-value]:
		--- < k > Identifier("sqrt") => builtin(Identifier("sqrt")) ...</ k >
		--- [structural] 
	rule [sqrt]:
		< k > prepareBuiltin((Identifier("sqrt")), tv(F:Float, double)) => tv(sqrtFloat(F:Float), double) ...</ k >
		[structural] 
	--------------------------------------------
	--- rule [log-is-value]:
		--- < k > Identifier("log") => builtin(Identifier("log")) ...</ k >
		--- [structural] 
	rule [log]:
		< k > prepareBuiltin((Identifier("log")), tv(F:Float, double)) => tv(logFloat(F:Float), double) ...</ k >
		[structural] 
	--------------------------------------------
	--- rule [exp-is-value]:
		--- < k > Identifier("exp") => builtin(Identifier("exp")) ...</ k >
		--- [structural] 
	rule [exp]:
		< k > prepareBuiltin((Identifier("exp")), tv(F:Float, double)) => tv(expFloat(F:Float), double) ...</ k >
		[structural] 
	--------------------------------------------
	--- rule [atan-is-value]:
		--- < k > Identifier("atan") => builtin(Identifier("atan")) ...</ k >
		--- [structural] 
	rule [atan]:
		< k > prepareBuiltin((Identifier("atan")), tv(F:Float, double)) => tv(atanFloat(F:Float), double) ...</ k >
		[structural] 
	--------------------------------------------
	--- rule [asin-is-value]:
		--- < k > Identifier("asin") => builtin(Identifier("asin")) ...</ k >
		--- [structural] 
	rule [asin]:
		< k > prepareBuiltin((Identifier("asin")), tv(F:Float, double)) => tv(asinFloat(F:Float), double) ...</ k >
		[structural] 
	--------------------------------------------
	--- rule [atan2-is-value]:
		--- < k > Identifier("atan2") => builtin(Identifier("atan2")) ...</ k >
		--- [structural] 
	rule [atan2]:
		< k > prepareBuiltin((Identifier("atan2")), (tv(F:Float, double) :: tv(F':Float, double))) => tv(atanFloat(F:Float, F':Float), double) ...</ k >
		[structural] 
	--------------------------------------------
	--- rule [tan-is-value]:
		--- < k > Identifier("tan") => builtin(Identifier("tan")) ...</ k >
	--- [structural] 
	rule [tan]:
		< k > prepareBuiltin((Identifier("tan")), tv(F:Float, double)) => tv(tanFloat(F:Float), double) ...</ k >
	[structural] 
	--------------------------------------------
	--- rule [floor-is-value]:
		--- < k > Identifier("floor") => builtin(Identifier("floor")) ...</ k >
	--- [structural] 
	rule [floor]:
		< k > prepareBuiltin((Identifier("floor")), tv(F:Float, double)) => tv(floorFloat(F:Float), double) ...</ k >
	[structural] 
	--------------------------------------------
	--- rule [cos-is-value]:
		--- < k > Identifier("cos") => builtin(Identifier("cos")) ...</ k >
	--- [structural] 
	rule [cos]:
		< k > prepareBuiltin((Identifier("cos")), tv(F:Float, double)) => tv(cosFloat(F:Float), double) ...</ k >
	[structural] 
	--------------------------------------------
	--- rule [fmod-is-value]:
		--- < k > Identifier("fmod") => builtin(Identifier("fmod")) ...</ k >
	--- [structural] 
	rule [fmod]:
		< k > prepareBuiltin((Identifier("fmod")), (tv(F:Float, double) :: tv(F':Float, double))) => tv(F:Float %Float F':Float, double) ...</ k >
	[structural] 
	--------------------------------------------
	--- rule [sin-is-value]:
		--- < k > Identifier("sin") => builtin(Identifier("sin")) ...</ k >
	--- [structural] 
	rule [sin]:
		< k > prepareBuiltin((Identifier("sin")), tv(F:Float, double)) => tv(sinFloat(F:Float), double) ...</ k >
	[structural] 
	--------------------------------------------
	--- rule [malloc-is-value]:
		--- < k > Identifier("malloc") => builtin(Identifier("malloc")) ...</ k >
	--- [structural] 

	rule [malloc]:
		< k > prepareBuiltin((Identifier("malloc")), tv(N:Nat, T:Type)) 
			=> alloc(Loc:Nat, N:Nat) ~> tv(Loc:Nat, pointerType(void)) 
		...</ k >
		< malloced >... (.).Map => Loc:Nat |-> N:Nat ...</ malloced >
		< nextLoc > Loc:Nat => inc(Loc:Nat) </ nextLoc >
		if T:Type ==Bool cfg:sizeut
	[structural] 
	--------------------------------------------
	--- Returns a pseudo-random integral number in the range 0 to RAND_MAX
	
	--- rule [rand-is-value]:
		--- < k > Identifier("rand") => builtin(Identifier("rand")) ...</ k >
	--- [structural] 
	--- unsignedIntegerTypes contains T:Type
	--- (2 ^Nat absInt(numBits(int)))
	--- fixme should use RAND_MAX
	rule [rand]:
		< k > prepareBuiltin((Identifier("rand")), Nil) 
			=> tv(absInt(randomRandom(Fresh:Nat)) %Int max(int), int)
		...</ k >
		< freshNat > Fresh:Nat => sNat(Fresh:Nat) </ freshNat >
	[structural] 
	--------------------------------------------
	--- rule [free-is-value]:
		--- < k > Identifier("free") => builtin(Identifier("free")) ...</ k >
	--- [structural] 
	
	rule [free]:
		< k > prepareBuiltin((Identifier("free")), tv(sym(Block:Nat) +Nat Offset:Nat, pointerType(?))) 
			=> skipval 
		...</ k >
		< mem >... Block:Nat |-> memblock(N:Nat, ?) => (.).Map ...</ mem >
		< malloced >... sym(Block:Nat) +Nat Offset:Nat |-> N:Nat => (.).Map ...</ malloced >
	[structural] 
	--------------------------------------------
	--- rule [calloc-is-value]:
		--- < k > Identifier("calloc") => builtin(Identifier("calloc")) ...</ k >
	--- [structural] 
	
	rule [calloc]:
		< k > prepareBuiltin((Identifier("calloc")), (tv(N:Nat, ?) :: tv(Size:Nat, ?))) 
			=> alloc(Loc:Nat, (N:Nat *Nat Size:Nat)) 
			~> zeroBlock(Loc:Nat)
			~> tv(Loc:Nat, pointerType(void)) 
		...</ k >
		< malloced >... (.).Map => Loc:Nat |-> (N:Nat *Nat Size:Nat) ...</ malloced >
		< nextLoc > Loc:Nat => inc(Loc:Nat) </ nextLoc >
	[structural] 
	--------------------------------------------
	--- rule [putchar-is-value]:
		--- < k > Identifier("putchar") => builtin(Identifier("putchar")) ...</ k >
	--- [structural] 
	--- fixme doesn't cast to int
	rule [putchar]:
		< k > prepareBuiltin((Identifier("putchar")), tv(N:Nat, ?)) => writeToFD(1, N:Nat) ~> tv(N:Nat, int) ...</ k >
	[structural] 
	-----------------------------------------
	--- rule [fslPutc-is-value]:
		--- < k > Identifier("fslPutc") => builtin(Identifier("fslPutc")) ...</ k >
	--- [structural] 
	--- fixme doesn't cast to int
	rule [fslPutc]:
		< k > prepareBuiltin((Identifier("fslPutc")), (tv(N:Nat, ?) :: tv(H:Nat, ?))) 
			=> writeToFD(H:Nat, N:Nat) 
			~> tv(N:Nat, int)
		...</ k >
	[structural] 
	--- --------------------------------------------
	--- rule [getchar-is-value]:
		--- < k > [getchar => builtin(getchar)] ...</ k >
	--- [structural] 
	--- --- fixme doesn't cast to int
	--- rule [getchar]:
		--- < k > [prepareBuiltin((getchar), Nil) => readFromFD(0)] ...</ k >
	--- [structural] 
	--- --------------------------------------------
	--- rule [fslFGetC-is-value]:
		--- < k > [fslFGetC => builtin(fslFGetC)] ...</ k >
	--- [structural] 
	--- --- fixme doesn't cast to int
	--- rule [fslFGetC]:
		--- < k > [prepareBuiltin((fslFGetC), (tv(FD:Nat, ?) :: tv(Offset:Nat, ?))) => readFromFD(FD:Nat, Offset:Nat)] ...</ k >
	--- [structural] 
	--------------------------------------------
	--- rule [fslCloseFile-is-value]:
		--- < k > Identifier("fslCloseFile") => builtin(Identifier("fslCloseFile")) ...</ k >
	--- [structural] 
	rule [fslCloseFile]:
		< k > prepareBuiltin((Identifier("fslCloseFile")), tv(FD:Nat, int)) => tv(0, int) ...</ k >
		< openFiles >... FD:Nat |-> ? => (.).Map ...</ openFiles >
	[structural] 
	--- --------------------------------------------
	--- rule [fslOpenFile-is-value]:
		--- < k > [fslOpenFile => builtin(fslOpenFile)] ...</ k >
	--- [structural] 
	--- rule [fslOpenFile]:
		--- < k > [prepareBuiltin((fslOpenFile), (Loc:Value :: tv(FD:Nat, int))) 
		--- => fsl-open-file(getString(Loc:Value), FD:Nat)] ...</ k >
	--- [structural] 
	
	--- op fsl-open-file-aux : String Nat String -> K 
	
	--- rule [fslOpenFile]:
		--- < k > [fsl-open-file(str(S:String), FD:Nat) => fsl-open-file-aux(S:String, FD:Nat, readFile(S:String))] ...</ k >
	--- [structural] 

		
	--- rule [fslOpenFile]:
		--- < k > [fsl-open-file-aux(Name:String, FD:Nat, Data:String) => tv(0, int)] ...</ k >
		--- < openFiles > [M:Map => M:Map[Name:String / FD:Nat]] </ openFiles >
		--- < files > [M':Map => M':Map[Data:String / Name:String]] </ files >
		--- if Data:String =/=Bool errorTCPSyntax
		--- andBool lengthString(Data:String) >=Nat 0
	--- [structural] 

	
	--- op fsl-open-file : K Nat -> K [metadata "strict(1)"] 
	--- op getString : K -> K 
	--- op getString : K String -> K [metadata "strict(1)"] 
	--- eq getString(K:K) = getString(K:K, "") 
	--- op str : String -> Value 
	--- rule [getString]:
		--- < k > [getString(tv(Loc:Nat, pointerType(T:Type)), S:String) 
		--- => getString(tv(sNat(Loc:Nat), pointerType(T:Type)), S:String +String charString(N:Nat))] ...</ k >
		--- < mem >... Loc:Nat |-> piece(N:Nat, 8) ...</ mem >
	--- if N:Nat =/=Bool 0 
	--- [structural] 
	--- rule [getString]:
		--- < k > [getString(tv(Loc:Nat, pointerType(?)), S:String) => str(S:String)] ...</ k >
		--- < mem >... Loc:Nat |-> piece(0, 8) ...</ mem >
	--- [structural] .	
	--- -----------------------------------------
	--- fixme: let's get rid of this asap, ok?
	--- rule [lib-printf-is-value]:
		--- < k > Identifier("printf") => builtin(Identifier("printf")) ...</ k >
	--- [structural] 
	

--- #define va_start(ap, pN)	\
---x ((ap) = ((va_list) (&pN) + __va_argsiz(pN)))
--- /*
 --- * End processing of variable argument list. In this case we do nothing
 --- */
--- #define va_end(ap)	((void)0)
--- /*
 --- * Increment ap to the next argument in the list while returing a
 --- * pointer to what ap pointed to first, which is of type t
 --- *
 --- * We cast to void* and then to t* because this avoids a warning about
 --- * increasing the alignment requirement
 --- */
--- #define va_arg(ap, t)					\
	 ---x (((ap) = (ap) + __va_argsiz(t)),		\
	  ---x *((t*) (void*) ((ap) - __va_argsiz(t))))	
	
	op printf-aux : Nat Nat List{C} -> K 
	op printf-string : Nat Nat -> K 
	op printf-% : K K List{C} -> K [strict(3)] --- K not nat, for context bug
	rule [lib-printf-start]:
		< k > prepareBuiltin((Identifier("printf")), (tv(Loc:Nat, pointerType(?)) :: L:List{C})) => printf-aux(0, Loc:Nat, L:List{C}) ...</ k >
	[structural] 
		
	rule [lib-printf-string]:
		< k > printf-string(Len:Nat, sym(Block:Nat) +Nat Offset:Nat) 
			=> writeToFD(1, N:Nat) 
			~> printf-string(sNat(Len:Nat), sym(Block:Nat) +Nat sNat(Offset:Nat)) 
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? Offset:Nat |-> piece(N:Nat, 8))) ...</ mem >
		if N:Nat =/=Bool 0
	[structural] 
	
	rule [lib-printf-string-done]:
		< k > printf-string(Len:Nat, sym(Block:Nat) +Nat Offset:Nat) => tv(Len:Nat, int) ...</ k >
		< mem >... Block:Nat |-> memblock(?, (? Offset:Nat |-> piece(0, 8))) ...</ mem >
	[structural] 
	
	---fixme why do i have to have the 0--255 check?
	rule [lib-printf-normal]:
		< k > printf-aux(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, L:List{C}) 
			=> writeToFD(1, N:Nat) ~> printf-aux(sNat(Len:Nat), sym(Block:Nat) +Nat sNat(Offset:Nat), L:List{C}) 
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? Offset:Nat |-> piece(N:Nat, 8))) ...</ mem >
		if N:Nat =/=Bool asciiCharString("%") 
		andBool N:Nat =/=Bool 0
		andBool N:Nat >=Nat 0 
		andBool N:Nat <=Nat 255
	[structural] 
	
	rule [lib-printf-done]:
		< k > printf-aux(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, L:List{C}) => tv(Len:Nat, int) ...</ k >
		< mem >... Block:Nat |-> memblock(?, (? Offset:Nat |-> piece(0, 8))) ...</ mem >
	[structural] 
	rule [lib-printf-null]:
		< k > printf-aux(0, sym(0) +Nat 0, Nil) => writeToFD(1, "(null)") ~> tv(6, int) ...</ k >
	[structural] 
	
	rule [lib-printf-%]:
		< k > printf-aux(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, L:List{C}) 
			=> printf-%(Len:Nat, sNat(sym(Block:Nat) +Nat Offset:Nat), L:List{C}) 
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if (N:Nat ==Bool asciiCharString("%"))
	[structural] 
	rule [lib-printf-%%]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, L:List{C}) 
			=> writeToFD(1, N:Nat) 
			~> printf-aux(sNat(Len:Nat), sNat(sym(Block:Nat) +Nat Offset:Nat), L:List{C}) ...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("%") 
	[structural] 
	--- fixme ignoring 0 flag for now
	rule [lib-printf-0]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, L:List{C}) 
			=> printf-%(Len:Nat, sNat(sym(Block:Nat) +Nat Offset:Nat), L:List{C}) 
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("0") 
	[structural] 
	--- ignoring num width
	rule [lib-printf-width]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, L:List{C}) 
			=> printf-%(Len:Nat, sNat(sym(Block:Nat) +Nat Offset:Nat), L:List{C}) 
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat >Int asciiCharString("0") 
		andBool N:Nat <=Int asciiCharString("9")
	[structural] 
	
	rule [lib-printf-%x]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, vararg(tv(Loc:Nat, ?)))
			=> printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, nextvarg(Loc:Nat, unsigned-int))
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("x") orBool N:Nat ==Bool asciiCharString("X") --- orBool N:Nat ==Bool asciiCharString("p")
	[structural]
	rule [lib-printf-%x]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, (vpair(tv(D:Int, unsigned-int), V:Value) :: ?)) 
			=> writeToFD(1, (if (lengthString(Rat2String(D:Int, 16)) ==Bool 1) then
				"0" +String Rat2String(D:Int, 16)
			else 
				Rat2String(D:Int, 16)
			fi)) ~> printf-aux(Len:Nat +Nat lengthString((if (lengthString(Rat2String(D:Int, 16)) ==Bool 1) then
				"0" +String Rat2String(D:Int, 16)
			else 
				Rat2String(D:Int, 16)
			fi)), sNat(sym(Block:Nat) +Nat Offset:Nat), V:Value) 
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("x") --- orBool N:Nat ==Bool asciiCharString("p")
	[structural] 
	
	--- fixme might be messing things up elsewhere
	op pointerToString : Nat -> String 
	eq pointerToString(sym(N:Nat) +Nat M:Nat) = "[sym(" +String Rat2String(N:Nat, 10) +String ") + " +String Rat2String(M:Nat, 10) +String "]" 
	eq pointerToString(NullPointer) = "NullPointer" 
		
	rule [lib-printf-%p]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, vararg(tv(Loc:Nat, ?)))
			=> printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, nextvarg(Loc:Nat, pointerType(void)))
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("p")
	[structural] 
	rule [lib-printf-%p]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, (vpair(tv(N':Nat, pointerType(void)), V:Value) :: ?)) 
			=> writeToFD(1, pointerToString(N':Nat))
			~> printf-aux(Len:Nat +Nat lengthString(pointerToString(N':Nat)), sNat(sym(Block:Nat) +Nat Offset:Nat), V:Value) 
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("p")
	[structural] 
	
	--- fixme tool bug, can't match one item in a C list
	--- below matches the rest of the list even though it's Nil, just to throw it away
	--- < k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, (vararg(tv(Loc:Nat, ?)) => nextvarg(Loc:Nat, int)))
	--- even printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, ((vararg(tv(Loc:Nat, ?)) :: L:List{C}) => nextvarg(Loc:Nat, int))) doesn't work
	--- probably not what i wrote above.  looks like it's heating nextvar, and when it cools, it's cooling down a :: 
	
	rule [lib-printf-%d]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, vararg(tv(Loc:Nat, ?)))
			=> printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, nextvarg(Loc:Nat, int))
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("d")
	[structural] 
	rule [lib-printf-%d]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, vpair(tv(D:Int, int), V:Value) :: ?) 
			=> writeToFD(1, Rat2String(D:Int, 10))
			~> printf-aux(Len:Nat +Nat lengthString(Rat2String(D:Int, 10)), sNat(sym(Block:Nat) +Nat Offset:Nat), V:Value) 
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("d")
	[structural] 
	
	rule [lib-printf-%u]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, vararg(tv(Loc:Nat, ?)))
			=> printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, nextvarg(Loc:Nat, unsigned-int))
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("u")
	[structural] 
	rule [lib-printf-%u]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, vpair(tv(D:Int, unsigned-int), V:Value) :: ?) 
			=> writeToFD(1, Rat2String(D:Int, 10))
			~> printf-aux(Len:Nat +Nat lengthString(Rat2String(D:Int, 10)), sNat(sym(Block:Nat) +Nat Offset:Nat), V:Value) 
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("u")
	[structural] 
	
	
	rule [lib-printf-%c]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, vararg(tv(Loc:Nat, ?))) 
			=> printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, nextvarg(Loc:Nat, int))
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("c") 
	[structural] 
	--- need to cast to unsigned-char
	rule [lib-printf-%c]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, (vpair(tv(C:Nat, int), V:Value) :: ?)) 
			=> writeToFD(1, C:Nat) 
			~> printf-aux(Len:Nat +Nat 1, sNat(sym(Block:Nat) +Nat Offset:Nat), V:Value) 
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("c") 
	[structural] 
	
	rule [lib-printf-%f]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, vararg(tv(Loc:Nat, ?))) 
			=> printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, nextvarg(Loc:Nat, double))
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("f") orBool N:Nat ==Bool asciiCharString("g") 
	[structural] 
	rule [lib-printf-%f]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, (vpair(tv(D:Float, double), V:Value) :: ?)) 
			=> writeToFD(1, Float2String(D:Float)) 
			~> printf-aux(Len:Nat +Nat lengthString(Float2String(D:Float)), sNat(sym(Block:Nat) +Nat Offset:Nat), V:Value) 
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("f") orBool N:Nat ==Bool asciiCharString("g") 
	[structural] 
	
	rule [lib-printf-%s]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, vararg(tv(Loc:Nat, ?))) 
			=> printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, nextvarg(Loc:Nat, pointerType(unsigned-char))) 
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("s") 
	[structural] 
	rule [lib-printf-%s]:
		< k > printf-%(Len:Nat, sym(Block:Nat) +Nat Offset:Nat, (vpair(tv(S:Nat, pointerType(unsigned-char)), V:Value) :: ?)) 
			=> printf-string(0, S:Nat)
			~> printf-aux(Len:Nat, sNat(sym(Block:Nat) +Nat Offset:Nat), V:Value) 
		...</ k >
		< mem >... Block:Nat |-> memblock(?, (? (Offset:Nat |-> piece(N:Nat, 8)))) ...</ mem >
		if N:Nat ==Bool asciiCharString("s") 
	[structural] 

	rule [lib-printf-%s-done]:
		< k > tv(Len':Nat, int) ~> printf-aux(Len:Nat, Loc:Nat, L:List{C}) 
			=> printf-aux(Len:Nat +Nat Len':Nat, Loc:Nat, L:List{C}) 
		...</ k >
	[structural] 
endkm
