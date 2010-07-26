kmod COMMON-C-SYNTAX is
	including PL-BOOL
	including PL-EXT-BOOL
	including PL-NAT
	including PL-INT
	including PL-RAT
	including PL-FLOAT
	including PL-STRING
	including PL-CONVERSION
	including PL-QID
	including PL-RANDOM
	including PL-ID
	
	--- op NULL : -> Id [ctor]
	--- op calloc : -> Id [ctor]
	--- op cos : -> Id [ctor]
	--- op sin : -> Id [ctor]
	--- op exit : -> Id [ctor]
	--- op free : -> Id [ctor]
	--- op main : -> Id [ctor]
	--- op malloc : -> Id [ctor]
	--- op printf : -> Id [ctor]
	--- op putchar : -> Id [ctor]
	--- op rand : -> Id [ctor]
	--- op sqrt : -> Id [ctor]
	--- op abort : -> Id [ctor]
	--- op debug : -> Id [ctor]
	--- op getchar : -> Id [ctor]
	--- op exp : -> Id [ctor]
	--- op log : -> Id [ctor]
	--- op atan : -> Id [ctor]
	--- op File-Scope : -> Id [ctor]
	
	--- op fslOpenFile : -> Id [ctor]
	--- op fslCloseFile : -> Id [ctor]
	--- op fslFGetC : -> Id [ctor]
	--- op fslPutc : -> Id [ctor]
	
	--- op longjmp : -> Id [ctor]
	--- op setjmp : -> Id [ctor]
	--- op floor : -> Id [ctor]
	--- op tan : -> Id [ctor]
	--- op fmod : -> Id [ctor]
	--- op atan2 : -> Id [ctor]
	--- op asin : -> Id [ctor]
	
	--- op spawn : -> Id [ctor]
	--- op sync : -> Id [ctor]
	--- op lock : -> Id [ctor]
	--- op unlock : -> Id [ctor]
	
	sort CabsLoc
	sort TypeSpecifier
	sort Storage
	sort FunSpecifier
	sort CVSpecifier
	sort SpecifierElem
	sort Specifier
	sort DeclType
	sort NameGroup
	sort FieldGroup
	sort InitNameGroup
	sort Name
	sort InitName
	sort SingleName
	sort EnumItem
	sort Definition
	sort Block
	sort AsmDetails
	sort Statement
	sort ForClause
	sort BinaryOperator
	sort UnaryOperator
	sort Expression
	sort Constant
	sort InitExpression
	sort InitWhat
	sort Attribute
	sort Program
	
	subsort TypeSpecifier < SpecifierElem --- because I flattened SpecifierElem
	
	
	--- lists
	sort List{Definition}
	subsort Definition < List{Definition}
	op _`,_ : List{Definition} List{Definition} -> List{Definition} [assoc id: NoDefinition]
	op NoDefinition : -> List{Definition}
	
	sort List{Attribute}
	subsort Attribute < List{Attribute} 
	
	sort List{FieldGroup}
	sort List{EnumItem}
	
	sort List{SingleName}
	subsort SingleName < List{SingleName}
	
	sort List{InitName}
	subsort InitName < List{InitName}
	
	sort List{SpecifierElem}
	subsort SpecifierElem < List{SpecifierElem}
	op _`,_ : List{SpecifierElem} List{SpecifierElem} -> List{SpecifierElem} [assoc id: NoSpecifierElem]
	op NoSpecifierElem : -> List{SpecifierElem}
	
	sort List{Name} 
	subsort Name < List{Name}
	op _`,_ : List{Name} List{Name} -> List{Name} [assoc id: NoName]
	op NoName : -> List{Name}
	
	--- Constructors 
	op CabsLoc : String Int Int Int -> CabsLoc
	op InitName : Name InitExpression -> InitName
	op Specifier : List{SpecifierElem} -> Specifier
	op NameGroup : Specifier List{Name} -> NameGroup

	op SpecTypedef : -> SpecifierElem
	
	--- --- --- op _`,_ : Specifier Sp
	
	--- --- ---sort List{SingleName}

	--- --- ---subsort SingleName < List{SingleName}
	--- op SingleNameList : SingleName -> SingleNameList
	
	op SingleName : Specifier Name -> SingleName
	
	--- op FunDef : SingleName Block CabsLoc CabsLoc -> DeclarationDefinition
	op DecDef : InitNameGroup CabsLoc -> Definition
	op TypeDef : NameGroup CabsLoc -> Definition
	
	op InitNameGroup : Specifier List{InitName} -> InitNameGroup

	op Prototype : DeclType List{SingleName} Bool -> DeclType
	op JustBase : -> DeclType
	op PointerType : List{Attribute} DeclType -> DeclType
	
	--- --- ---sort List{Attribute}
	
	--- --- ---subsort List{Attribute} < AttributeList
	--- --- ---subsort Attribute < List{Attribute}

	--- --- ---op _`,_ : List{Attribute} List{Attribute} -> List{Attribute} [assoc id:List{Attribute}]
	--- --- ---opList{Attribute} : -> List{Attribute}
	--- --- ---op AttributeList : List{Attribute} -> AttributeList
	op NoAttributes : -> List{Attribute}

	op NoInit : -> InitExpression
	
	op Name : Id DeclType List{Attribute} CabsLoc -> Name
	
	op Identifier : String -> Id
	op #NoName : -> Id
	
	
	***(
	syntax TypeSpecifier ::= Void | Char | Bool | Short | Int | Long 
							--- | int64
							| Float | Double | Signed | Unsigned
	***)
	
	ops Void Char Bool Short Int Long Float Double Signed Unsigned : -> TypeSpecifier [ctor]
	op Named : String -> TypeSpecifier [ctor]
	op StructRef : String List{Attribute} -> TypeSpecifier [ctor]
	op StructDef : String List{FieldGroup} List{Attribute} -> TypeSpecifier [ctor]
	op UnionRef : String List{Attribute} -> TypeSpecifier [ctor]
	op UnionDef : String List{FieldGroup} List{Attribute} -> TypeSpecifier [ctor]
	op EnumRef : String List{Attribute} -> TypeSpecifier [ctor]
	op EnumDef : String List{EnumItem} List{Attribute} -> TypeSpecifier [ctor]
	op TypeOfE : Expression -> TypeSpecifier [ctor]
	op TypeOfT : Specifier DeclType -> TypeSpecifier [ctor]
		
	
	--- sort List{DeclarationDefinition}
	--- subsort DeclarationDefinition < List{DeclarationDefinition}
	op Program : List{Definition} -> Program
	

***(
type typeSpecifier = (* Merge all specifiers into one type *)
    Tvoid                             (* Type specifier ISO 6.7.2 *)
  | Tchar
  | Tbool
  | Tshort
  | Tint
  | Tlong
  | Tint64
  | Tfloat
  | Tdouble
  | Tsigned
  | Tunsigned
  | Tnamed of string
  (* each of the following three kinds of specifiers contains a field 
   * or item list iff it corresponds to a definition (as opposed to
   * a forward declaration or simple reference to the type); they
   * also have a list of __attribute__s that appeared between the
   * keyword and the type name (definitions only) *)
  | Tstruct of string * field_group list option * attribute list
  | Tunion of string * field_group list option * attribute list
  | Tenum of string * enum_item list option * attribute list
  | TtypeofE of expression                      (* GCC __typeof__ *)
  | TtypeofT of specifier * decl_type       (* GCC __typeof__ *)

and storage =
    NO_STORAGE | AUTO | STATIC | EXTERN | REGISTER

and funspec = 
    INLINE | VIRTUAL | EXPLICIT

and cvspec =
    CV_CONST | CV_VOLATILE | CV_RESTRICT

(* Type specifier elements. These appear at the start of a declaration *)
(* Everywhere they appear in this file, they appear as a 'spec_elem list', *)
(* which is not interpreted by cabs -- rather, this "word soup" is passed *)
(* on to the compiler.  Thus, we can represent e.g. 'int long float x' even *)
(* though the compiler will of course choke. *)
and spec_elem =
    SpecTypedef          
  | SpecCV of cvspec            (* const/volatile *)
  | SpecAttr of attribute       (* __attribute__ *)
  | SpecStorage of storage
  | SpecInline
  | SpecType of typeSpecifier
  | SpecPattern of string       (* specifier pattern variable *)

(* decided to go ahead and replace 'spec_elem list' with specifier *)
and specifier = spec_elem list


(* Declarator type. They modify the base type given in the specifier. Keep
 * them in the order as they are printed (this means that the top level
 * constructor for ARRAY and PTR is the inner-level in the meaning of the
 * declared type) *)
and decl_type =
 | JUSTBASE                               (* Prints the declared name *)
 | PARENTYPE of attribute list * decl_type * attribute list
                                          (* Prints "(attrs1 decl attrs2)".
                                           * attrs2 are attributes of the
                                           * declared identifier and it is as
                                           * if they appeared at the very end
                                           * of the declarator. attrs1 can
                                           * contain attributes for the
                                           * identifier or attributes for the
                                           * enclosing type.  *)
 | ARRAY of decl_type * attribute list * expression
                                          (* Prints "decl [ attrs exp ]".
                                           * decl is never a PTR. *)
 | PTR of attribute list * decl_type      (* Prints "* attrs decl" *)
 | PROTO of decl_type * single_name list * bool 
                                          (* Prints "decl (args[,..])".
                                           * decl is never a PTR.*)

(* The base type and the storage are common to all names. Each name might
 * contain type or storage modifiers *)
(* e.g.: int x, y; *)
and name_group = specifier * name list

(* The optional expression is the bitfield *)
and field_group = specifier * (name * expression option) list

(* like name_group, except the declared variables are allowed to have initializers *)
(* e.g.: int x=1, y=2; *)
and init_name_group = specifier * init_name list

(* The decl_type is in the order in which they are printed. Only the name of
 * the declared identifier is pulled out. The attributes are those that are
 * printed after the declarator *)
(* e.g: in "int *x", "*x" is the declarator; "x" will be pulled out as *)
(* the string, and decl_type will be PTR([], JUSTBASE) *)
and name = string * decl_type * attribute list * cabsloc

(* A variable declarator ("name") with an initializer *)
and init_name = name * init_expression

(* Single names are for declarations that cannot come in groups, like
 * function parameters and functions *)
and single_name = specifier * name


and enum_item = string * expression * cabsloc
***)	
	
	
***(
(*
** Declaration definition (at toplevel)
*)
and definition =
   FUNDEF of single_name * block * cabsloc * cabsloc
 | DECDEF of init_name_group * cabsloc        (* global variable(s), or function prototype *)
 | TYPEDEF of name_group * cabsloc
 | ONLYTYPEDEF of specifier * cabsloc
 | GLOBASM of string * cabsloc
 | PRAGMA of expression * cabsloc
 | LINKAGE of string * cabsloc * definition list (* extern "C" {.. } *)
 (* toplevel form transformer, from the first definition to the *)
 (* second group of definitions *)
 | TRANSFORMER of definition * definition list * cabsloc
 (* expression transformer: source and destination *)
 | EXPRTRANSFORMER of expression * expression * cabsloc


(* the string is a file name, and then the list of toplevel forms *)
and file = string * definition list


(*
** statements
*)

(* A block contains a list of local label declarations ( GCC's ({ __label__ 
 * l1, l2;.. }) ) , a list of definitions and a list of statements  *)
and block = 
    { blabels: string list;
      battrs: attribute list;
      bstmts: statement list
    } 

(* GCC asm directives have lots of extra information to guide the optimizer *)
and asm_details =
    { aoutputs: (string option * string * expression) list; (* optional name, constraints and expressions for outputs *)
      ainputs: (string option * string * expression) list; (* optional name, constraints and expressions for inputs *)
      aclobbers: string list (* clobbered registers *)
    }

and statement =
   NOP of cabsloc
 | COMPUTATION of expression * cabsloc
 | BLOCK of block * cabsloc
 | SEQUENCE of statement * statement * cabsloc
 | IF of expression * statement * statement * cabsloc
 | WHILE of expression * statement * cabsloc
 | DOWHILE of expression * statement * cabsloc
 | FOR of for_clause * expression * expression * statement * cabsloc
 | BREAK of cabsloc
 | CONTINUE of cabsloc
 | RETURN of expression * cabsloc
 | SWITCH of expression * statement * cabsloc
 | CASE of expression * statement * cabsloc
 | CASERANGE of expression * expression * statement * cabsloc
 | DEFAULT of statement * cabsloc
 | LABEL of string * statement * cabsloc
 | GOTO of string * cabsloc
 | COMPGOTO of expression * cabsloc (* GCC's "goto *exp" *)
 | DEFINITION of definition (*definition or declaration of a variable or type*)

 | ASM of attribute list * (* typically only volatile and const *)
          string list * (* template *)
          asm_details option * (* extra details to guide GCC's optimizer *)
          cabsloc

   (** MS SEH *)
 | TRY_EXCEPT of block * expression * block * cabsloc
 | TRY_FINALLY of block * block * cabsloc
 
and for_clause = 
   FC_EXP of expression
 | FC_DECL of definition

(*
** Expressions
*)
and binary_operator =
    ADD | SUB | MUL | DIV | MOD
  | AND | OR
  | BAND | BOR | XOR | SHL | SHR
  | EQ | NE | LT | GT | LE | GE
  | ASSIGN
  | ADD_ASSIGN | SUB_ASSIGN | MUL_ASSIGN | DIV_ASSIGN | MOD_ASSIGN
  | BAND_ASSIGN | BOR_ASSIGN | XOR_ASSIGN | SHL_ASSIGN | SHR_ASSIGN

and unary_operator =
    MINUS | PLUS | NOT | BNOT | MEMOF | ADDROF
  | PREINCR | PREDECR | POSINCR | POSDECR

and expression =
    NOTHING
  | UNARY of unary_operator * expression
  | LABELADDR of string  (* GCC's && Label *)
  | BINARY of binary_operator * expression * expression
  | QUESTION of expression * expression * expression

   (* A CAST can actually be a constructor expression *)
  | CAST of (specifier * decl_type) * init_expression

    (* There is a special form of CALL in which the function called is
       __builtin_va_arg and the second argument is sizeof(T). This 
       should be printed as just T *)
  | CALL of expression * expression list
  | COMMA of expression list
  | CONSTANT of constant
  | PAREN of expression
  | VARIABLE of string
  | EXPR_SIZEOF of expression
  | TYPE_SIZEOF of specifier * decl_type
  | EXPR_ALIGNOF of expression
  | TYPE_ALIGNOF of specifier * decl_type
  | INDEX of expression * expression
  | MEMBEROF of expression * string
  | MEMBEROFPTR of expression * string
  | GNU_BODY of block
  | EXPR_PATTERN of string     (* pattern variable, and name *)

and constant =
  | CONST_INT of string   (* the textual representation *)
  | CONST_FLOAT of string (* the textual representaton *)
  | CONST_CHAR of int64 list
  | CONST_WCHAR of int64 list
  | CONST_STRING of string
  | CONST_WSTRING of int64 list 
    (* ww: wstrings are stored as an int64 list at this point because
     * we might need to feed the wide characters piece-wise into an 
     * array initializer (e.g., wchar_t foo[] = L"E\xabcd";). If that
     * doesn't happen we will convert it to an (escaped) string before
     * passing it to Cil. *) 

and init_expression =
  | NO_INIT
  | SINGLE_INIT of expression
  | COMPOUND_INIT of (initwhat * init_expression) list

and initwhat =
    NEXT_INIT
  | INFIELD_INIT of string * initwhat
  | ATINDEX_INIT of expression * initwhat
  | ATINDEXRANGE_INIT of expression * expression
 

                                        (* Each attribute has a name and some
                                         * optional arguments *)
and attribute = string * expression list
	
	
***)	
	
	
	
	--- ---- A.1.5 Constants
	--- --- 6.4.4
	--- sort Constant
	--- --- subsort Integer-Constant Character-Constant Enumeration-Constant < Constant
	--- subsort Integer-Constant Floating-Constant < Constant
	
	--- --- 6.4.4.1
	--- sort Integer-Constant
	--- subsort Int < Integer-Constant
	--- op @U : Integer-Constant -> Integer-Constant
	--- op @L : Integer-Constant -> Integer-Constant
	--- op @UL : Integer-Constant -> Integer-Constant
	--- op @LL : Integer-Constant -> Integer-Constant
	--- op @ULL : Integer-Constant -> Integer-Constant
	
	--- op hex : String -> Integer-Constant

	
	--- --- subsort Decimal-Constant < Integer-Constant
	--- --- Octal-Constant Hexadecimal-Constant 
	--- --- TODO
	
	--- --- sort Decimal-Constant
	--- --- subsort Int < Decimal-Constant
	--- --- TODO
	
	--- --- sort Octal-Constant
	--- --- TODO
	
	--- --- sort Hexadecimal-Constant
	--- --- TODO
	
	--- --- TODO
	
	--- --- 6.4.4.2
	--- sort Floating-Constant
	--- subsort Float < Floating-Constant
	--- --- subsort Decimal-Floating-Constant Hexadecimal-Floating-Constant < Floating-Constant
	--- op @F : Floating-Constant -> Floating-Constant
	--- op @L : Floating-Constant -> Floating-Constant
	
	--- --- sort Decimal-Floating-Constant
	--- --- TODO
	
	--- --- sort Hexadecimal-Floating-Constant
	--- --- TODO
	
	--- --- TODO
	
	--- --- 6.4.4.3
	--- --- sort Enumeration-Constant
	--- --- subsort Id < Enumeration-Constant
	
	--- --- 6.4.4.4
	--- --- sort Character-Constant
	--- --- TODO
	
	--- --- 6.4.5
	--- sort String-Literal
	--- subsort String < String-Literal
	--- --- TODO
	
	--- --- TODO
	
	---- A.2.1 Expressions
	--- 6.5.1
	--- subsort Id Constant String-Literal < Expression
	***(
	--- 6.5.2
	op _`[_`] : Expression Expression -> Expression [prec 21]
	--- op _`(_`) : Postfix-Expression List{Assignment-Expression} -> Postfix-Expression [strict renameTo apply]
	---op _`(_`) : Expression Expression-List -> Expression
	
	--- these should be strict but doesn't quite do the right thing
	op Apply : Expression List{Expression} -> Expression
	op Apply : Expression -> Expression
	--- op _`(`) : Postfix-Expression -> Postfix-Expression [strict renameTo applyNil]
	op _._ : Expression Id -> Expression [prec 21] --- not strict in 1 because of _._ and arrays
	op _->_ : Expression Id -> Expression [prec 21 metadata "strict(1)"]
	op _++ : Expression -> Expression [prec 21]
	op _-- : Expression -> Expression [prec 21]
	--- op `(_`)`{_`} : Type-Name Initializer-List -> Postfix-Expression
	--- op `(_`)`{_`,`} : Type-Name Initializer-List -> Postfix-Expression

	sort List{Expression}
	subsort Expression < List{Expression}
	opList{Expression} : -> List{Expression} [metadata "latex(renameTo \\ensuremath{\\kdot})"]
	op _.,._ : List{Expression} List{Expression} -> List{Expression} [assoc id:List`{Expression`}]

	--- 6.5.3
	--- sizeof, &, ++,, --, and all assignment operators are NOT STRICT
	--- C99 6.3.2.1
	ops ++_ --_ : Expression -> Expression [prec 22]
	op &_ : Expression -> Expression [prec 22 metadata "latex(renameTo \\ensuremath{\\&}_)"]
	---op *_ : Expression -> Expression [prec 22]
	op Deref : Expression -> Expression [metadata "strict"]
	---op +_ : Expression -> Expression [prec 22]
	op -un_ : Expression -> Expression [prec 22 metadata "strict"]
	op ~_ : Expression -> Expression [prec 22 metadata "strict"]
	op !_ : Expression -> Expression [prec 22 metadata "strict"]
	op sizeof : Expression -> Expression
	
	--- 6.5.4
	op Cast : Type-Name Expression -> Expression [metadata "strict"]
	ops _*_ _/_ _%_ : Expression Expression -> Expression [prec 31 gather(E e) metadata "strict"]	
	ops _+_ _-_ : Expression Expression -> Expression [prec 33 gather(E e) metadata "strict"]
	ops _<<_ _>>_ : Expression Expression -> Expression [prec 35 gather(E e) metadata "strict"]
	ops _<_ _>_ _<=_ _>=_ : Expression Expression -> Expression [prec 37 gather(E e) metadata "strict"]
	ops _==_ _!=_ : Expression Expression -> Expression [prec 39 gather(E e) metadata "strict"]
	op _&binop_ : Expression Expression -> Expression [prec 41 gather(E e) metadata "strict latex(renameTo _\\ensuremath{\\&}_)"]
	op _^_ : Expression Expression -> Expression [prec 43 gather(E e) metadata "strict"]
	op _|_ : Expression Expression -> Expression [prec 45 gather(E e) metadata "strict"]
	op _&&_ : Expression Expression -> Expression [prec 47 gather(E e) metadata "strict(1) latex(renameTo _\\ensuremath{\\&\\&}_)"]
	op _||_ : Expression Expression -> Expression [prec 49 gather(E e) metadata "strict(1)"]
	op _?_:_ : Expression Expression Expression -> Expression [prec 51 gather(e & E)]
	
	--- 6.5.16
	ops _*=_ _/=_ _%=_ _+=_ _-=_ _<<=_ _>>=_ _^=_ _|=_ : Expression Expression -> Expression [prec 53]
	ops _&binop=_ : Expression Expression -> Expression [prec 53 metadata "latex(renameTo _\\ensuremath{\\&=}_)"]
	--- op _=_ : Unary-Expression Assignment-Expression -> Assignment-Expression
	op _:=_ : Expression Expression -> Expression [prec 53 metadata "strict(2)"]
			
	--- 6.5.17
	sort Expression
	
	---- A.2.2 Declarations
	--- 6.7
	sort Declaration
	---op Actual-Declaration : Declaration -> Declaration [metadata "strict"]
	op Local : Declaration -> Declaration [metadata "strict"]
	op Declaration : SeqList -> Declaration [metadata "strict"]
	op Declaration : SeqList Init-Declarator-List -> Declaration [metadata "strict(1)"]
	op Typedef : SeqList Declarator -> Declaration [metadata "strict(1)"]
	
	sort Init-Declarator-List
	subsort Init-Declarator < Init-Declarator-List
	subsort Init-Declarator < Block-Item

	---subsort Type-Specifier Type-Qualifier Function-Specifier < Declaration-Specifiers
	---subsort Storage-Class-Specifier Type-Specifier < Declaration-Specifiers
	subsort Type-Specifier Storage-Class-Specifier < SeqList
	
	sort Init-Declarator

	subsort Declarator < Init-Declarator
	op _=_ : Declaration Expression -> Init-Declarator [metadata "strict(1)"]
	op _=`{_`} : Declaration List{Expression} -> Init-Declarator [metadata "strict(1) latex(renameTo _\\ensuremath{=\\{_\\}})"]
	
	--- 6.7.1
	sort Storage-Class-Specifier
	ops typedef extern static auto register : -> Storage-Class-Specifier
	op inline : -> Storage-Class-Specifier --- nonstandard
		
	--- 6.7.2
	sort Type-Specifier
	sort Base-Type
	subsort Typedef-Name Struct-Or-Union-Specifier Enum-Specifier Base-Type < Type-Specifier
	op typedefName : Id -> Typedef-Name
	ops void 
		no-type
		float 
		double
		long-double
		short-int unsigned-short-int
		char unsigned-char signed-char 
		int unsigned-int
		short unsigned-short
		long-int unsigned-long-int
		long unsigned-long
		long-long unsigned-long-long
		long-long-int unsigned-long-long-int
		: -> Base-Type [ctor]
	op Pointer : Type-Specifier -> Type-Specifier [metadata "strict(1)"] 
	
	----ops `_Bool `_Complex : -> Type-Specifier [ctor]
	--- TODO
	
	--- 6.7.2.1
	sort Struct-Or-Union-Specifier
	--- Note: CIL gives names to all anonymous struct/unions
	---op struct`{_`} : SeqList -> Struct-Or-Union-Specifier
	---op union`{_`} : Struct-Declaration-List -> Struct-Or-Union-Specifier
	
	op structDef : Id List{Parameter} -> Struct-Or-Union-Specifier [metadata "strict(2)"]
	op unionDef : Id List{Parameter} -> Struct-Or-Union-Specifier [metadata "strict(2)"]
	op structDef : Id -> Struct-Or-Union-Specifier
	op unionDef : Id -> Struct-Or-Union-Specifier	
	op struct : Id -> Struct-Or-Union-Specifier
	op union : Id -> Struct-Or-Union-Specifier
		
	sort Struct-Declaration
	op Field : SeqList Declarator -> Struct-Declaration [metadata "strict(1)"].
	subsort Struct-Declaration < List{Parameter}
	
	subsort Type-Specifier < SeqList

	--- sort Struct-Declarator
	--- TODO subsort Declarator < Struct-Declarator
	--- op :_ : Constant-Expression -> Struct-Declarator
	--- op _:_ : Declarator Constant-Expression -> Struct-Declarator
	
	--- 6.7.2.2
	sort Enum-Specifier
	--- Note: CIL gives names to anonymous enums
	--- op enum`{_`} : Enumerator-List -> Enum-Specifier
	---op enum_`{_`} : Id List{Expression} -> Enum-Specifier
	op enum : Id List{Expression} -> Enum-Specifier
	--- op enum`{_`,`} : Enumerator-List -> Enum-Specifier
	--- op enum_`{_`,`} : Identifier Enumerator-List -> Enum-Specifier
	---op enum_ : Id -> Enum-Specifier
	op enum : Id -> Enum-Specifier
	
	--- 6.7.3
	--- sort Type-Qualifier
	--- ops const restrict volatile : -> Type-Qualifier [ctor]
	
	---6.7.4
	--- sort Function-Specifier
	--- op inline : -> Function-Specifier [ctor]
	
	--- 6.7.5
	sort Declarator

	sort Direct-Declarator

	subsort Direct-Declarator < Declarator
	subsort Direct-Declarator < Expression

	subsort Type-Specifier < Direct-Declarator

	subsort Id < Direct-Declarator
	op Pointer : Direct-Declarator -> Direct-Declarator [metadata "strict(1)"]
	op Pointer : Direct-Declarator Direct-Declarator -> Direct-Declarator [metadata "strict(1)"]
	op Pointer`(`) : -> Direct-Declarator
	--- op _`[`] : Declarator -> Declarator
	op _`[_`] : Direct-Declarator Expression -> Direct-Declarator [ditto]
	--- op _`[__`] : Declarator Type-Qualifier-List Assignment-Expression -> Declarator
	--- op _`[static_`] : Declarator Assignment-Expression -> Declarator
	--- op _`[static__`] : Declarator Type-Qualifier-List Assignment-Expression -> Declarator
	--- op _`[_static_`] : Declarator Type-Qualifier-List Assignment-Expression -> Declarator
	--- op _`[*`] : Declarator -> Declarator
	--- op _`[_*`] : Declarator Type-Qualifier-List -> Declarator
	--- op _`(_`) : Direct-Declarator Parameter-Type-List -> Direct-Declarator --- Ex: main(void)
	op Direct-Function-Declarator : Direct-Declarator Parameter-Type-List -> Direct-Declarator
	op Direct-Function-Declarator : Parameter-Type-List -> Direct-Declarator
	op BitField : Expression -> Direct-Declarator
	op BitField : Declarator Expression -> Direct-Declarator
	
	sort Parameter-Type-List
	sort List{Parameter}
	subsort Parameter-Declaration < List{Parameter}
	opList{Parameter} : -> List{Parameter} [metadata "latex(renameTo \\ensuremath{\\kdot})"]
	op _,.,_ : List{Parameter} List{Parameter} -> List{Parameter} [assoc id:List`{Parameter`}]
	op Parameter-Type-List : List{Parameter} -> Parameter-Type-List [metadata "strict"]
	op Parameter-Type-List`(`) : -> Parameter-Type-List

	sort Parameter-Declaration
	op Pointer : SeqList -> SeqList
	op.. : -> Parameter-Declaration
	
	--- fixme
	--- same label, two different strictnesses
	op Parameter-Declaration : SeqList -> Parameter-Declaration [metadata "strict"]
	op Parameter-Declaration : SeqList Declarator -> Parameter-Declaration [metadata "strict(1)"]
	
	--- 6.7.6
	sort Type-Name
	subsort SeqList < Type-Name
	sort SeqList
	op __ : SeqList SeqList -> SeqList [prec 85]
	subsort Declarator < SeqList
	
	--- 6.7.7
	sort Typedef-Name
	
	--- 6.7.8
	op Initializer : Expression -> Expression
	op InitList : List{Expression} -> Expression
	op InitItem : Expression -> Expression
	--- op `{_`,`} : Initializer-List -> Initializer
	---op _,_ : Initializer-List Initializer-List -> Initializer-List [assoc]
	
	--- sort Designation
	--- op _= : Designator-List -> Designation
	op Designation : Expression Expression -> Expression
	--- sort Designator-List
	--- TODO subsort Designator < Designator-List
	--- TODO op __ : Designator-List Designator -> Designator-List
	
	--- sort Designator	
	--- op `[_`] : Constant-Expression -> Designator
	--- op_ : Identifier -> Designator
	op ArrayDesignator : Expression -> Expression
	op FieldDesignator : Id -> Expression
	
	---- A.2.3 Statements
	--- 6.8
	sort Statement
	
	subsort Labeled-Statement Jump-Statement Compound-Statement Iteration-Statement Expression-Statement Selection-Statement < Statement
		
	--- 6.8.1
	sort Labeled-Statement
	op _:_ : Id SeqList -> Labeled-Statement
	op case`(_`)_:_ : Nat Expression SeqList -> Labeled-Statement [metadata "strict(2)"]
	op default`(_`):_ : Nat SeqList -> Labeled-Statement
	
	--- 6.8.2
	sort Compound-Statement

	op Block : SeqList -> Compound-Statement
	op Block`(`) : -> Compound-Statement

	subsort Block-Item < SeqList
	sort Block-Item
	
	subsort Statement < Block-Item
	subsort Declaration < Block-Item
	---op _; : Declaration -> Block-Item [prec 75 metadata "strict"]
	
	--- 6.8.3
	sort Expression-Statement
	op EmptyStatement`; : -> Expression-Statement	
	op _; : Expression -> Expression-Statement [prec 75 metadata "strict"]
	
	--- 6.8.4
	sort Selection-Statement

	op if`(_`)_ : Expression Statement -> Selection-Statement [metadata "strict(1)"]
	op if`(_`)_else_ : Expression Statement Statement -> Selection-Statement [metadata "strict(1)"]
	op switch`(_`)`(_`)_ : Nat Expression Statement -> Selection-Statement [metadata "strict(2)"]
	
	--- 6.8.5
	sort Iteration-Statement

	op while`(_`)_ : Expression Statement -> Iteration-Statement

	--- 6.8.6
	sort Jump-Statement

	op goto_; : Id -> Jump-Statement
	op continue`; : -> Jump-Statement [format (ni o o)]
	op break`; : -> Jump-Statement [format (ni o o)]
	op return`; : -> Jump-Statement
	op return_; : Expression -> Jump-Statement [metadata "strict"]
	
	---- A.2.4 External definitions
	--- 6.9
	---sort Translation-Unit
	subsort SeqList < Program

	sort External-Declaration
	subsort External-Declaration < SeqList

	subsort Function-Definition < External-Declaration
	op Global : SeqList -> External-Declaration [metadata "strict"]
	op Global`(`) : -> External-Declaration
	
	--- 6.9.1
	sort Function-Definition
	
	--- Note: Totally made up to help parsing
	op _`{_`} : Declaration SeqList -> Function-Definition [prec 70 format (ni o++ no --in d) metadata "strict(1) latex(renameTo _\\ensuremath{\\{_\\}})"]
	***)
endkm
