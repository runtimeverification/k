***(

maybe say something like
< k > label(?,, arrayType(T:Type) => pointerType(T:Type) ,, ?)
breaks toEval-aux
***)



--- why isn't K ~> K proper?
--- arithmetic on a void * pointer
--- argument of function type
--- need one past array
--- 6.7.5.3:11 if, in a parameter declaration, an identifier can be treated either as a typedef name or as a parameter name, it shall be taken as a typedef name
--- switch with only one case?
--- casting from unsigned long long int to int is super slow
--- pr34099.c checks if anding unknown with 0 is 0.  need to add named unknowns and better interpret

--- pr44828.c demonstrates slow conversion between large nums to small signed types

***(
 a beaut
  int a = 0;
  int *p;
  size_t b;
  b = (size_t)(p = &(int []){0, 1, 2}[++a]);
  if (a != 1 || *p != 1 || *(int *)b != 1)
    abort ();
***)

***(
--- fixme
union U
{
  int i, j[4];
} u = {};

what are j bits?  spec says padding bits are zeroed, but doesn't say about bits not in first id
***)


--- fixme not handling this
--- N1494 6.7.2.1:13 An unnamed member of structure type with no tag is called an anonymous structure; an unnamed member of union type with no tag is called an anonymous union. The members of an anonymous struct or union are considered to be members of the containing structure or union. This applies recursively if the containing structure or union is also an anonymous structure or union

--- take address of builtins

--- extern inside block that shadows variable in a function that shadows global extern

--- c1x 6.7.9:5 If the declaration of an identifier has block scope, and the identifier has external or internal linkage, the declaration shall have no initializer for the identifier
--- this means you can't have initializers for static variables??

---C99 6.7.8:10 If an object has static duration ... if it has pointer type, it is NULL, if it is arithmetic, 0, aggregate, recursively these, union, first member by these

--- switch on enum :(

--- § 6.6.3/2

    --- Flowing off the end of a function is equivalent to a return with no value; this results in undefined behavior in a value-returning function

--- § 3.6.1/5

    --- If control reaches the end of main without encountering a return statement, the effect is that of executing
    --- return 0;


--- enums should probably be handled more generically so that they can be evaluated anywhere

***( 
not handling this type:
static union {
  unsigned char buf[MAX_LENGTH];
  long long align_int;
  long double align_fp;
} u1, u2;

("Field").KProperLabel(unsigned-char,,("_`[_`]").KProperLabel("Id"(buf),,("_+_").KProperLabel(("_+_").KProperLabel(("_+_").KProperLabel(("sizeof").KProperLabel(long-long-int),,("_*_").KProperLabel(("tv").KResultLabel(8,,unsigned-long-int),,("sizeof").KProperLabel(long-long-int))),,("sizeof").KProperLabel(long-long-int)),,("tv").KResultLabel(2,,unsigned-long-int)))) 
***)

---zzz set print attribute on 
kmod INCOMING-MODULES is
	including K 
	including C-SYNTAX 
	including C-CONFIGURATION 
	including K-CONTEXTS 
	including K-PROPER 
	including K-QUOTED-LABELS 
endkm

kmod COMMON-SEMANTIC-SYNTAX is
	including INCOMING-MODULES 
	
	sort Formula 
	subsort Formula < K 
	
	op True : -> Formula 
	op False : -> Formula 
	op _/\_ : Formula Formula -> Formula 
	op _\/_ : Formula Formula -> Formula 
	
	op List : BagItem -> ListItem 
	op ListToK : List -> K 
	op Map : Map -> K 
	op piece : Nat Nat -> Nat 
	op trueUnknown : -> Nat [ctor] 
	
	op unknown : Nat -> Nat [ctor] 
	
	--- fixme could presumably have more of these to simulate behavior, but you usually don't know what.  for example, 1 & unknown = unknown
	--- eq 1 |Int piece(unknown(Len:Nat), Len:Nat)) = 1 .  --- bad, bitwise
	
	op unknownF : -> Float [ctor] 
	op skipval : -> KResult 
	op debugK : -> K 
	op discard : -> K 
	op File-Scope : -> Id [ctor] 
	op unnamedBitField : -> Id [ctor] 
	op bignum : -> Type 
	op debug : -> K 
	op sym : Nat -> Nat 
	op byteo : Nat -> Nat 
	op bito : Nat -> Nat 
	eq bito(0) = 0 --- FIXME need to check this is okay in all circumstances
	op bitoffset : Nat -> Nat 
	op byteoffset : Nat -> Nat 
	op declare : K K -> K [metadata "strict(1)"] 
	op enumItem : Id Value -> Value 
	op resolveReferences : -> K 
	
	op toString : K -> String 
	
	op maxType : Type Type -> Type 
	
	op bitRange : Nat Nat Nat -> Nat --- original number, from, to inclusive
	
	op fillToBytes : K -> K [metadata "strict(1)"] 
	
	op floorLoc : Nat -> Nat --- loc with possible bit offset returning base byte	
	op readFunction : Nat -> K 
	
	ceq _bit::_(piece(N:Nat, Len:Nat), piece(N':Nat, Len':Nat)) 
		= piece((N:Nat <<Nat Len':Nat) |Nat N':Nat, Len:Nat +Nat Len':Nat)
		if N:Nat >=Nat 0 andBool N':Nat >=Nat 0 
	eq _bit::_(piece(0, 0), N:Nat) = N:Nat 
	eq piece(piece(N:Nat, Len:Nat), Len:Nat) = piece(N:Nat, Len:Nat) 
	
	op innerType : Type -> Type
	
	op AttributeValue : String List{C} -> KResult 
	
	op extractBitsFromList : K Nat Nat -> K [metadata "strict(1)"] --- data, offset, size in bits
	op typedef : Id -> Id 
	op unnamed : Nat -> Id 
	
	op NullPointerConstant : -> Nat 
	eq NullPointerConstant = 0 
	op NullPointer : -> Nat 
	
	op emptyValue : -> Value 
	op _bit::_ : Nat Nat -> Nat [assoc] 
	op allocate : Type K -> K
	
	op zero : K -> K 
	op zeroBlock : Nat -> K 
		
	op value : K -> K 
	eq value(tv(V:List{K}, ?)) = V:List{K} 
	
	op type : K -> Type 
	eq type(tv(?, T:Type)) = T:Type 
	
	op allocateType : Nat Type -> K 
	op allocateTypeIfAbsent : Nat Type -> K 
	op giveType : Id Type -> K 
	op addToEnv : Id Nat -> K 
	
	op read : K K -> K [metadata "strict(2)"] --- location, type
	op write : K K -> K [metadata "strict(2)"] --- location, value

	op isTypeCompatible : K K -> Bool 
	
	op hasBeenPromoted : Type -> Bool 
	
	op bitloc : Nat Nat Nat -> Nat 
	op inc : Nat -> Nat 
	op initialize : Id Type K -> K 
	op memblock : Nat Map -> K --- length and an array from offsets to bytes
	
	op listToK : K -> K 
	op klistToK : List{K} -> K 
	op UnknownCabsLoc : -> K 
	
	--- Basic types
	ops bool : -> BaseType 
	ops void bool char short-int int long-int long-long-int : -> BaseType 
	ops float double long-double : -> BaseType 
	ops signed-char unsigned-char : -> BaseType 
	ops unsigned-short-int unsigned-int unsigned-long-int unsigned-long-long-int : -> BaseType 
	op no-type : -> BaseType 
	
	--- Composite types
	op enumType : Id -> BaseType [ctor] 
	op arrayType : Type Nat -> Type [ctor] 
	op incompleteArrayType : Type -> Type [ctor] 
	op flexibleArrayType : Type -> Type [ctor] 
	op bitfieldType : Type Nat -> Type [ctor] 
	op functionType : Type List{Type} -> Type [ctor] 
	op pointerType : Type -> Type [ctor] 
	op structType : Id -> Type [ctor] 
	op unionType : Id -> Type [ctor] 
	op qualifiedType : Type K -> Type [ctor] 
	
	op unqualifyType : K -> Type --- takes a type, but sometimes things like maps give K
	
	--- these aren't real types, but are values that can appear in type contexts
	op prototype : Type -> Type 
	op typedefType : Id Type -> Type 
	op variadic : -> Type 

	subsort Type < C 
	subsort Value < C 
	sort BaseValue 

	subsort Nat Int Rat Float < BaseValue 
	subsort BaseValue < C 
	subsort BaseValue < Builtins 
	op dataList : List{K} -> KResult 
	subsort Value < KResult K 
	subsort Type < KResult K 
	sort BaseType 
	subsort BaseType < Type Builtins 
	
	op sizeofType : K -> K [metadata "strict"] --- generates a tv(size, cfg:sizeut)
	op bitSizeofType : K -> K [metadata "strict"] 
	op byteSizeofType : K -> K [metadata "strict"] 
	op bitsToBytes : Nat -> Nat 
	op HOLE : -> Expression 
	op l : KLabel -> K [metadata "builtin wrapper"] 
	op _contains_ : Set K -> Bool [memo] 
	--- Types
	op typedDeclaration : Type Id -> Type --- would rather this be KResult, but can't get the subsorting to work
	
	--- op testing : -> Set [memo] 
	--- eq testing =  Set(
		--- l('arrayType),, 
		--- l('bitfieldType),, 
		--- l('functionType)
	--- ) 
	
	
	sort Type 
	sort Value 
	sort List{Type} 
	subsort List{Type} < KResult 
	subsort List{Type} < List{C} 
	subsort Type < List{Type} 
	subsort Type < List{C} 
	subsort Value < List{Type} 
	op _::_ : List{Type} List{Type} -> List{Type} [ditto metadata "ditto"] 
	op Nil : -> List{Type} [ditto] 
	
	op setOfTypes : -> Set [memo] 
***(zzz
	eq setOfTypes = Set(
		l('arrayType),, 
		l('bitfieldType),, 
		l('functionType),, 
		l('pointerType),, l('structType),, l('unionType),, 
		l('qualifiedType)
	)
	***)
	
	op bind : List{C} List{Type} -> K 
	op tv : List{K} Type -> Value 
	op concretize : Type K -> K [metadata "strict(2)"] 
	op functionObject : Id Type K -> Value 
	op functionPrototype : Id Type -> Value 
	op DeclType : K K -> K [metadata "strict(1)"] --- represents a type before canonicalization.  as in "int *x", first arg is "Int", second arg is "PointerType(JustBase)"
	
	op firstChar : String -> Char 
	op nthChar : String Nat -> Char 
	op butFirstChar : String -> String 
	op charToAscii : String -> Nat 
	op stringToChar : String -> Char 
	op asciiCharString : String -> Nat 
	
	op _to_ : Nat Nat -> List{K} 
	op cast : K K -> K [metadata "strict"] --- as described in 6.3
	op arithInterpret : Type BaseValue -> K --- interpret the result of arithmetic as in 6.5.4
	op interpret : Type K -> K --- interpret the values of reading from mem
	op leftShiftInterpret : Type BaseValue K -> K 
	op rightShiftInterpret : Type BaseValue -> K 
	
	op integerTypes : -> Set [memo] 
	op unsignedIntegerTypes : -> Set [memo] 
	op signedIntegerTypes : -> Set [memo] 
	op hasIntegerType : Type -> Bool [memo] 
	op hasFloatType : Type -> Bool [memo] 
	op hasUnsignedIntegerType : Type -> Bool [memo] 
	op hasSignedIntegerType : Type -> Bool [memo] 
	
	op typeof : K -> K 
	op writeToFD : Nat Nat -> K 
	op writeToFD : Nat String -> K 
	op readFromFD : Nat -> K 
	op readFromFD : Nat Nat -> K 

	op calculateLength : List{Type} -> K 
	op calculateGotoMap : Id K -> K 
	
	op hasCharType : Type -> Bool 
	--- fixme make sure i use this everywhere instead of T:BaseType
	op isABaseType_ : K -> Bool 
	op hasPointerType : Type -> Bool 
	op hasArrayType : Type -> Bool 
	op hasBoolType : Type -> Bool 
	op hasStructType : Type -> Bool 
	op hasUnionType : Type -> Bool 
	op hasAggregateType : Type -> Bool 
	op hasFunctionType : Type -> Bool 
	op hasFunctionPointerType : Type -> Bool 
	op hasBitfieldType : Type -> Bool 
	op hasExternType : Type -> Bool 
	op hasStaticType : Type -> Bool 
	op hasIncompleteType : Type -> Bool 
	op hasTypedefType : Type -> Bool 
	
	op kpair : K K -> K 
	op promote : K -> K 
	op extractField : List{K} Type Id -> K 
	op allocString : Nat String -> K 
	op sequencePoint : -> K 
	
	op handleBuiltin : Id Type -> K 
	
	op min : Type -> Int [memo] 
	op max : Type -> Int [memo] 
	op storeNew_atLoc_ : K Nat -> K [metadata "strict(1)"] 
	op store_atLoc_ : K Nat -> K [metadata "strict(1)"] 
	op alloc : K K -> K --- should be K K 
	
	--- these are also used by compound literals
	op initializerValue : Id Type K -> KResult 
	op figureInitializer : Id K K -> K [metadata "strict(2)"] --- id, type, initializer
	
	
endkm

kmod C-SETTINGS is
	including INCOMING-MODULES 
	including COMMON-SEMANTIC-SYNTAX 

	op IdentifierSet : List{K} -> Set 
	eq IdentifierSet((S:String,, L:List{K})) = SetItem(Identifier(S:String)) IdentifierSet(L:List{K}) 
	op builtinIdentifiers : -> Set [memo] 
	
	--- fixme bug why can't i use (.).List{K} here?
	eq builtinIdentifiers = IdentifierSet((
		"abort"
		,, "asin"
		,, "atan"
		,, "atan2"
		,, "calloc"
		,, "cos"
		,, "debug"
		,, "exit"
		,, "exp"
		,, "floor"
		,, "fmod"
		,, "free"
		,, "fslCloseFile"
		,, "fslFGetC"
		,, "fslOpenFile"
		,, "fslPutc"
		,, "getchar"
		,, "log"
		,, "longjmp"
		,, "malloc"
		,, "printf"
		,, "putchar"
		,, "rand"
		,, "setjmp"
		,, "sin"
		,, "sqrt"
		,, "tan"
	)) 
	
	--- S 6.2.5 p.35 i.15.  "The implementation shall define char to have the same range, representation, and behavior as either signed char or unsigned char.  37)... Irrespective of the choice made, char is a separate type from the other two and is not compatible with either
	--- fixme I'm not sure what consequence being a separate type entails, so for now it will just be rewritten to the chosen type
	rule char => signed-char 
		[structural] 

	op numBitsPerByte : -> NzNat 
	op numBytes : Type -> Nat [memo] 
	op numBits : Type -> Nat [memo] 

	eq numBitsPerByte = 8 
	
	eq numBytes(bool) = 1 
	eq numBytes(signed-char) = 1 
	eq numBytes(short-int) = 2 
	eq numBytes(int) = 4 
	eq numBytes(long-int) = 4 
	eq numBytes(long-long-int) = 8 
	
	eq numBytes(float) = 4 
	eq numBytes(double) = 8 
	eq numBytes(long-double) = 16 
	
	eq numBytes(enumType(X:Id)) = numBytes(int) 
	
	op cfg:sizeut : -> Type 
	eq cfg:sizeut = unsigned-long-int 
	
	op cfg:largestUnsigned : -> Type 
	eq cfg:largestUnsigned = unsigned-long-long-int 

	op cfg:ptrsize : -> Nat 
	eq cfg:ptrsize = 4 
	
	op cfg:ptrdiffut : -> Type 
	eq cfg:ptrdiffut = int 
	
	eq min(enumType(?)) = min(int) 
	eq max(enumType(?)) = max(int) 
	
	--- — number of bits for smallest object that is not a bit-field (byte)
	--- CHAR_BIT 8
	--- — minimum value for an object of type signed char
	--- SCHAR_MIN -127 // -(27 - 1)
	--- — maximum value for an object of type signed char
	--- SCHAR_MAX +127 // 27 - 1
	--- — maximum value for an object of type unsigned char
	--- UCHAR_MAX 255 // 28 - 1
	--- — minimum value for an object of type char
	--- CHAR_MIN see below
	--- — maximum value for an object of type char
	--- CHAR_MAX see below
	--- — maximum number of bytes in a multibyte character, for any supported locale
	--- MB_LEN_MAX 1
	--- — minimum value for an object of type short int
	--- SHRT_MIN -32767 // -(215 - 1)
	--- — maximum value for an object of type short int
	--- SHRT_MAX +32767 // 215 - 1
	--- — maximum value for an object of type unsigned short int
	--- USHRT_MAX 65535 // 216 - 1
	--- — minimum value for an object of type int
	--- INT_MIN -32767 // -(215 - 1)
	--- — maximum value for an object of type int
	--- INT_MAX +32767 // 215 - 1
	--- — maximum value for an object of type unsigned int
	--- UINT_MAX 65535 // 216 - 1
	--- — minimum value for an object of type long int
	--- LONG_MIN -2147483647 // -(231 - 1)
	--- — maximum value for an object of type long int
	--- LONG_MAX +2147483647 // 231 - 1
	--- — maximum value for an object of type unsigned long int
	--- ULONG_MAX 4294967295 // 232 - 1
	--- — minimum value for an object of type long long int
	--- LLONG_MIN -9223372036854775807 // -(263 - 1)
	--- — maximum value for an object of type long long int
	--- LLONG_MAX +9223372036854775807 // 263 - 1
	--- — maximum value for an object of type unsigned long long int
	--- ULLONG_MAX 18446744073709551615 // 264 - 1
	
	op rank : Type -> Int 
	
	--- fixme, this is kind of cheating as it will promote bitfields smaller than int to int leave others unchanged
	--- ceq rank(bitfieldType(?, N:Nat)) = 0 
		--- if N:Nat < numBits(int) 
		
	eq rank(bool) = 0 
	eq rank(char) = 1 
	eq rank(signed-char) = 1 
	eq rank(unsigned-char) = 1 
	eq rank(short-int) = 2 
	eq rank(unsigned-short-int) = 2 
	eq rank(int) = 3 
	eq rank(unsigned-int) = 3 
	eq rank(long-int) = 4 
	eq rank(unsigned-long-int) = 4 
	eq rank(long-long-int) = 5 
	eq rank(unsigned-long-long-int) = 5 
	
	eq rank(bignum) = 100 --- used for internal calculation.  should be bigger than all other ranks
	
	eq rank(enumType(?)) = rank(int) 
	---C99 6.3.1.1
	
	***(
	--- no two signed are the same
	rank of signed shall be greater than rank of signed with less precision
	rank(long-long-int) > rank(long int) > rank(int) > rank(short int) > rank(signed-char)
	rank unsigned is same as signed
	rank(char) == rank(signed char) == rank(unsigned-char)
	rank(_Bool) < rank(char)
	rank(enumType) == rank compatible int type
	transitive
	***)
endkm

kmod SEMANTIC-HELPERS is 
	including COMMON-SEMANTIC-SYNTAX 
	including C-SETTINGS 
	
	op isConcreteNumber : Int -> Bool 
	eq isConcreteNumber(sym(?) +Nat ?) = false 
	eq isConcreteNumber(bito(?) +Nat ?) = false 
	ceq isConcreteNumber(I:Int) = true
		if  I:Int <=Int 0 orBool I:Int >Int 0 
	
	--- this should probably go in the k prelude
	op _in_ : K List -> Bool 
	eq K:K in (ListItem(K:K) ?) = true 
	eq K:K in (.).List = false 
	ceq K:K in (ListItem(K':K) L:List) = K:K in L:List
		if K:K =/=Bool K':K 
	
	
	rule [discard]:
		< k > V:Value ~> discard => .K ...</ k >
		[structural] 
	
	---- derived
	eq bitsToBytes(N:Nat) = absInt(ceilingRat(N:Nat /Rat numBitsPerByte)) 
		
	eq numBytes(unsigned-char) = numBytes(signed-char) 
	eq numBytes(unsigned-short-int) = numBytes(short-int) 
	eq numBytes(unsigned-int) = numBytes(int) 
	eq numBytes(unsigned-long-int) = numBytes(long-int) 
	eq numBytes(unsigned-long-long-int) = numBytes(long-long-int) 
	
	***(zzz
	ceq numBits(T:Type) = numBytes(T:Type) *Nat numBitsPerByte 
		if getKLabel(T:Type) =/=Bool 'bitfieldType 
	***)
	eq numBits(bitfieldType(?, N:Nat)) = N:Nat 

	eq min(bool) = 0 
	eq max(bool) = 1 
	
	eq min(signed-char) = -Int (2 ^Nat absInt(_-Int_(numBits(signed-char), 1))) 
	eq max(signed-char) = _-Int_(2 ^Nat absInt(_-Int_(numBits(signed-char), 1)), 1) 
	eq min(short-int) = -Int (2 ^Nat absInt(_-Int_(numBits(short-int), 1))) 
	eq max(short-int) = _-Int_(2 ^Nat absInt(_-Int_(numBits(short-int), 1)), 1) 
	eq min(int) = -Int (2 ^Nat absInt(_-Int_(numBits(int), 1))) 
	eq max(int) = _-Int_(2 ^Nat absInt(_-Int_(numBits(int), 1)), 1) 
	eq min(long-int) = -Int (2 ^Nat absInt(_-Int_(numBits(long-int), 1))) 
	eq max(long-int) = _-Int_(2 ^Nat absInt(_-Int_(numBits(long-int), 1)), 1) 
	eq min(long-long-int) = -Int (2 ^Nat absInt(_-Int_(numBits(long-long-int), 1))) 
	eq max(long-long-int) = _-Int_(2 ^Nat absInt(_-Int_(numBits(long-long-int), 1)), 1) 
	
	eq min(unsigned-char) = 0 
	eq max(unsigned-char) = _-Int_(2 ^Nat absInt(numBits(unsigned-char)), 1) 
	eq min(unsigned-short-int) = 0 
	eq max(unsigned-short-int) = _-Int_(2 ^Nat absInt(numBits(unsigned-short-int)), 1) 
	eq min(unsigned-int) = 0 
	eq max(unsigned-int) = _-Int_(2 ^Nat absInt(numBits(unsigned-int)), 1) 
	eq min(unsigned-long-int) = 0 
	eq max(unsigned-long-int) = _-Int_(2 ^Nat absInt(numBits(unsigned-long-int)), 1) 
	eq min(unsigned-long-long-int) = 0 
	eq max(unsigned-long-long-int) = _-Int_(2 ^Nat absInt(numBits(unsigned-long-long-int)), 1) 
	
	
	eq stringToChar(C:Char) = C:Char 
	eq asciiCharString(S:String) = asciiString(stringToChar(S:String)) 
	rule [firstChar]:
		firstChar(S:String) => substrString(S:String, 0, 1)
		[structural] 
	rule [nthChar]:
		nthChar(S:String, N:Nat) => substrString(S:String, N:Nat, 1)
		[structural] 
	rule [charToAscii]:
		charToAscii(C:Char) => asciiString(C:Char)
		[structural] 
	rule [butFirstChar]:
		butFirstChar(S:String) => substrString(S:String, 1, lengthString(S:String))
		[structural] 
		
	eq N:Nat to N:Nat = .List{K} 
	ceq N:Nat to N':Nat = (N:Nat,,((N:Nat +Nat 1) to N':Nat))
		if N:Nat <Nat N':Nat 

	--- Note: it only makes sense to memo this if the sets are just used to represent categories
	eq S:Set SetItem(K:K) contains K:K = true 
	ceq S:Set SetItem(K1:K) contains K2:K = S:Set contains K2:K 
		if K1:K =/=Bool K2:K 
	eq (.).Set contains K:K = false 

	eq hasIntegerType(T:Type) = hasUnsignedIntegerType(T:Type) orBool hasSignedIntegerType(T:Type) 
	
	ceq hasUnsignedIntegerType(T:Type) = true
		if (unsignedIntegerTypes contains T:Type) 
***(zzz
	ceq hasUnsignedIntegerType(T:Type) = false 
		if getKLabel(T:Type) =/=Bool 'bitfieldType
		andBool setOfTypes contains l(getKLabel(T:Type)) 
	ceq hasUnsignedIntegerType(bitfieldType(T:Type, ?)) = true 
		if hasUnsignedIntegerType(T:Type) ==Bool true 
	ceq hasUnsignedIntegerType(bitfieldType(T:Type, ?)) = false 
		if hasUnsignedIntegerType(T:Type) ==Bool false 
	
	ceq hasSignedIntegerType(T:Type) = true
		if (signedIntegerTypes contains T:Type) 
	eq hasSignedIntegerType(enumType(?)) = true --- choice fixme
	ceq hasSignedIntegerType(T:Type) = false 
		if getKLabel(T:Type) =/=Bool 'bitfieldType
		andBool setOfTypes contains l(getKLabel(T:Type)) 
	ceq hasSignedIntegerType(bitfieldType(T:Type, ?)) = true 
		if hasSignedIntegerType(T:Type) ==Bool true 
	ceq hasSignedIntegerType(bitfieldType(T:Type, ?)) = false 
		if hasSignedIntegerType(T:Type) ==Bool false 
***)
	ceq min(bitfieldType(T:Type, N:Nat)) = 0
		if hasUnsignedIntegerType(T:Type) 
	ceq max(bitfieldType(T:Type, N:Nat)) = _-Int_(2 ^Nat absInt(N:Nat), 1)
		if hasUnsignedIntegerType(T:Type) 
	
	ceq min(bitfieldType(T:Type, N:Nat)) = -Int (2 ^Nat absInt(_-Int_(N:Nat, 1)))
		if hasSignedIntegerType(T:Type) 
	ceq max(bitfieldType(T:Type, N:Nat)) = _-Int_(2 ^Nat absInt(_-Int_(N:Nat, 1)), 1) 
		if hasSignedIntegerType(T:Type) 
endkm

kmod COMMON-INCLUDE is
	including INCOMING-MODULES 
	including SEMANTIC-HELPERS 
	including C-SETTINGS 
	including COMMON-SEMANTIC-SYNTAX
endkm

kmod C-SEMANTICS-MISC is
	including COMMON-INCLUDE 
	
	eq inc(sym(N:Nat) +Nat M:Nat) = sym(N:Nat +Nat 1) +Nat M:Nat 
	eq sNat(sym(N:Nat) +Nat M:Nat) = sym(N:Nat) +Nat (M:Nat +Nat 1) 
	ceq I:Int +Int (N:Nat +Nat sym(M:Nat))
		= absInt(N:Nat +Int I:Int) +Nat sym(M:Nat) 
		if N:Nat +Int I:Int >=Int 0 
		
	ceq (N:Nat +Nat sym(M:Nat)) -Int I:Int
		= absInt(N:Nat -Int I:Int) +Nat sym(M:Nat) 
		if N:Nat -Int I:Int >=Int 0 
		
	rule
		< k > sequencePoint => .K ...</ k >
		< locsWrittenTo > ? => (.).Bag </ locsWrittenTo >
		[structural] 
		
	--- ---C99 6.5.3.2 (p79) footnote 90) Thus, &*E == E; &(E1[E2]) == (E1 + E2)
	
	--- ---C99 6.5.3.2 90) ... It is always true that if E is a function designator or an lvalue that is a valid operand of the u of the unary & operator, *&E is a function designator or an lvalue equal to E

	eq calculateLength(Nil) = 0 
	eq calculateLength(T:Type :: L:List{Type}) = calculateLength(T:Type) + calculateLength(L:List{Type}) 
	eq calculateLength(typedDeclaration(T:Type, ?)) = bitSizeofType(T:Type) 
	
	op extractField-pre : List{K} Type K K -> K [metadata "strict(3 4)"] 
	op extractField-aux : List{K} Type Nat Nat List{K} -> K 
	
	--- figureOffset(loc(0, 0), calcStructSize-aux(L1:List{KResult}, 0), T:Type)
	rule [extractField-from-struct-start]:
		< k > extractField(L:List{K}, structType(S:Id), F:Id)
			=> extractField-pre(L:List{K}, T:Type, calculateLength(L:List{Type}), bitSizeofType(T:Type)) ...</ k >
		< structs >... S:Id |-> (L:List{Type} :: typedDeclaration(T:Type, F:Id) :: ?:List{Type}) ...</ structs >
		[structural] 
		
	rule [extractField-from-union-start]:
		< k > extractField(L:List{K}, unionType(S:Id), F:Id)
			=> extractField-pre(L:List{K}, T:Type, tv(0, unsigned-long-int), bitSizeofType(T:Type)) ...</ k >
		< structs >... S:Id |-> (?:List{Type} :: typedDeclaration(T:Type, F:Id) :: ?:List{Type}) ...</ structs >
		[structural] 
		
	rule
		< k > extractField-pre(L:List{K}, T:Type, tv(Offset:Nat, ?), tv(Len:Nat, ?))
			=> concretize(T:Type, fillToBytes(extractBitsFromList(dataList(L:List{K}), Offset:Nat, Len:Nat)))
		...</ k >
		[structural] 
				
	rule [writeToFD-char]:
		< k > writeToFD(FD:Nat, N:Nat) => .K ...</ k >
		< openFiles >... FD:Nat |-> Filename:String ...</ openFiles >
		< files >... Filename:String |-> (S:String => S:String +String charString(N:Nat %Nat 256)) ...</ files >
		[structural] 
	rule [writeToFD-string]:
		< k > writeToFD(FD:Nat, S':String) => .K ...</ k >
		< openFiles >... FD:Nat |-> Filename:String ...</ openFiles >
		< files >... Filename:String |-> (S:String => S:String +String S':String) ...</ files >
		[structural] 
	--- rule [readFromFD-char]:
		--- < k > [readFromFD(FD:Nat) => tv(charToAscii(firstChar(S:String)), int)]  ...</ k >
		--- < openFiles >... FD:Nat |-> Filename:String ...</ openFiles >
		--- < files >... Filename:String |-> [S:String => butFirstChar(S:String)] ...</ files >
		--- if S:String =/=Bool ""
		--- [structural] 
		
	--- rule
		--- < k > [readFromFD(FD:Nat, Offset:Nat) => tv(charToAscii(nthChar(S:String, Offset:Nat)), int)]  ...</ k >
		--- < openFiles >... FD:Nat |-> Filename:String ...</ openFiles >
		--- < files >... Filename:String |-> S:String ...</ files >
		--- if lengthString(S:String) >Nat Offset:Nat
		--- [structural] 
	--- rule
		--- < k > [readFromFD(FD:Nat, Offset:Nat) => tv(-1, int)]  ...</ k >
		--- < openFiles >... FD:Nat |-> Filename:String ...</ openFiles >
		--- < files >... Filename:String |-> S:String ...</ files >
		--- if lengthString(S:String) <=Nat Offset:Nat
		--- [structural] 

	eq listToK(K:K) = klistToK(getList{K}(K:K)) 
	eq klistToK((K:K,, L:List{K})) = K:K ~> klistToK(L:List{K}) 
	--- eq klistToK((K:K)) = K:K 
	--- eq klistToK(.) = . 
	eq klistToK(.List{K}) = .K
	
	eq CabsLoc("cabs loc unknown", -10, -10, 0) = UnknownCabsLoc 
	
	
	--- TODO nicely handle loc range instead of ignoring L2
	--- fixme feature i'd like to say ? instead of k, but context transformers don't work that way
	rule
		< k > DefinitionLocRange(K:K, L1:CabsLoc, L2:CabsLoc) => K:K ...</ k >
		< currentProgramLoc > ? => L1:CabsLoc </ currentProgramLoc >
		[structural] 
	rule [DefinitionLoc]:
		< k > DefinitionLoc(K:K, L:CabsLoc) => K:K ...</ k >
		< currentProgramLoc > ? => L:CabsLoc </ currentProgramLoc >
		[structural] 
	rule [StatementLoc]:
		< k > StatementLoc(K:K, L:CabsLoc) => K:K ...</ k >
		< currentProgramLoc > ? => L:CabsLoc </ currentProgramLoc >
		[structural] 
	rule [EnumItemLoc]:
		< k > EnumItemLoc(K:K, L:CabsLoc) => K:K ...</ k >
		< currentProgramLoc > ? => L:CabsLoc </ currentProgramLoc >
		[structural] 
		
	rule [Attributes]:
		< k > Attribute(S:String, L:List{C}) => AttributeValue(S:String, L:List{C}) ...</ k >
		[structural]
		
	eq AttributeWrapper(K:K, ?) = K:K 
	eq NameLoc(K:K, ?) = K:K 
	
	ceq N:Nat +Nat bito(M:Nat) = N:Nat +Nat (M:Nat /Nat numBitsPerByte) +Nat bito(M:Nat %Nat numBitsPerByte)
		if M:Nat >=Nat numBitsPerByte 
	
	--- this maintains byte order
	op fillToBytes-aux : K List{K} -> K 
	eq fillToBytes(dataList(L:List{K})) = fillToBytes-aux(dataList(L:List{K}), .List{K}) 
	ceq fillToBytes-aux(dataList((L:List{K},, piece(N:Nat, Len:Nat))), L':List{K}) 
		= fillToBytes-aux(dataList(L:List{K}), (piece(N:Nat, Len:Nat),, L':List{K}))
		if Len:Nat ==Bool numBitsPerByte 
	
	ceq fillToBytes-aux(dataList(piece(N:Nat, Len:Nat)), L':List{K})
		= fillToBytes-aux(dataList((piece(0, 1),, piece(N:Nat, Len:Nat))), L':List{K})
		if Len:Nat <Nat numBitsPerByte 
		
	ceq fillToBytes-aux(dataList((L:List{K},, piece(N:Nat, Len:Nat),, piece(N':Nat, Len':Nat))), L':List{K}) 
		= fillToBytes-aux(dataList((L:List{K},, piece(_bit::_(piece(N:Nat, Len:Nat), piece(N':Nat, Len':Nat)), Len:Nat +Nat Len':Nat))), L':List{K})
		if Len:Nat +Nat Len':Nat <=Nat numBitsPerByte 
				
	eq fillToBytes-aux(dataList(.List{K}), L:List{K})
		= dataList(L:List{K}) 
		
	--- coallesce bitranges that are adjacent
	ceq _bit::_(piece(bitRange(N:Nat, sNat(To:Nat), To':Nat), Len:Nat), piece(bitRange(N:Nat, From:Nat, To:Nat), Len':Nat)) 
		= piece(bitRange(N:Nat, From:Nat, To':Nat), Len:Nat +Nat Len':Nat) 
		if Len:Nat +Nat Len':Nat <=Nat numBitsPerByte 
	
	eq piece(N:Nat bit:: N':Nat, Len:Nat) bit:: piece(N'':Nat, Len':Nat)
		= piece(N:Nat bit:: N':Nat bit:: piece(N'':Nat, Len':Nat), Len:Nat +Nat Len':Nat) 

	eq piece(N'':Nat, Len':Nat) bit:: piece(N:Nat bit:: N':Nat, Len:Nat)
		= piece(piece(N'':Nat, Len':Nat) bit:: N:Nat bit:: N':Nat, Len:Nat +Nat Len':Nat) 

	ceq bitRange(N:Nat bit:: piece(?, Len:Nat), Pos:Nat, Pos:Nat)
		= bitRange(N:Nat, absInt(Pos:Nat -Int Len:Nat), absInt(Pos:Nat -Int Len:Nat))
		if Pos:Nat >Nat 0
		andBool Pos:Nat -Int Len:Nat >=Int 0 
		
	eq bitRange(? bit:: piece(N:Nat, 1), 0, 0) = piece(N:Nat, 1) 
	eq bitRange(piece(N:Nat, 1), 0, 0) = piece(N:Nat, 1) 
		
	ceq bitRange(piece(bitRange(N:Nat, Start:Nat, End:Nat), Len:Nat), 0, 0)
		= bitRange(piece(bitRange(N:Nat, Start:Nat, Start:Nat), 1), 0, 0) 
		if Start:Nat +Nat Len:Nat ==Bool sNat(End:Nat) 
	
	ceq bitRange(N:Nat, Pos:Nat, Pos:Nat) = 1 &Nat (N:Nat >>Nat Pos:Nat)
		if N:Nat >=Nat 0 
	ceq bitRange(piece(N:Nat, 1), Pos:Nat, Pos:Nat) = 1 &Nat (N:Nat >>Nat Pos:Nat)
		if N:Nat >=Nat 0 
		
	ceq bitRange(N:Nat, 0, To:Nat) = N:Nat
		if sNat(To:Nat) ==Bool numBitsPerByte 
	
	ceq bitRange(? bit:: piece(N:Nat, Len:Nat), Start:Nat, End:Nat) 
		= bitRange(piece(N:Nat, Len:Nat), Start:Nat, End:Nat)
		if sNat(End:Nat) <=Nat Len:Nat 
	
	eq bitRange(piece(N:Nat, sNat(End:Nat)), 0, End:Nat)
		= piece(N:Nat, sNat(End:Nat)) 
	eq bitRange(? bit:: piece(N:Nat, sNat(End:Nat)), 0, End:Nat)
		= piece(N:Nat, sNat(End:Nat)) 
		
	ceq bitRange(piece(N:Nat, Len:Nat), Pos:Nat, Pos:Nat) = (N:Nat >>Nat Pos:Nat) &Nat 1
		if N:Nat >=Nat 0 
		
	eq Identifier("___missing_field_name") = #NoName 
endkm

load common-c-conversions
load common-c-expressions
load common-c-statements
load common-c-standard-lib
load common-c-typing
load common-c-memory
load common-c-declarations

kmod COMMON-C-SEMANTICS is
	including COMMON-INCLUDE 
	including C-SEMANTICS-MISC 
	
	including COMMON-C-TYPING 
	including COMMON-C-DECLARATIONS 
	including COMMON-C-MEMORY 
	including COMMON-C-STATEMENTS 
	including COMMON-C-EXPRESSIONS 
	including COMMON-C-CONVERSIONS 
	including COMMON-C-STANDARD-LIBRARY 
	
	op eval : K -> Bag 
	op eval : K List{K} String -> Bag 
endkm
