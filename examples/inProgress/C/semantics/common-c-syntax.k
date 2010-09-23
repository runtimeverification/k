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
	including K
	
	op AttributeWrapper : K List{C} -> C --- new
	
	--- The resulting sorts can really be replaced with K, but i've left them in for now since they don't hurt anything and are somewhat documenting
	
	--- Sorts directly from CABS
	sort CabsLoc
	sort TypeSpecifier
	sort Storage
	--- sort FunSpecifier --- not used, even by cabs
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
	sort PureStatement
	sort PureEnumItem
	sort ForClause
	--- sort BinaryOperator --- not used by us
	--- sort UnaryOperator --- not used by us
	sort Expression
	sort Constant
	sort InitExpression
	sort InitWhat
	sort Attribute
	
	--- Additional sorts
	sort Program
	sort TranslationUnit
	sort IntConstant
	sort InitFragment
	sort FieldName
	sort PureDefinition
	
	sort C
	sort List{C}
	subsort Id < C
	op Nil : -> List{C}
	subsort C < List{C}
	op _::_ : List{C} List{C} -> List{C} [hybrid strict assoc id: Nil]
	
	subsort SpecifierElem < KResult
	--- sort List{SpecifierElem} 
	--- subsort List{SpecifierElem} < KResult
	--- op _::_ : List{SpecifierElem} List{SpecifierElem} -> List{SpecifierElem} [assoc id: Nil]
	--- op Nil : -> List{SpecifierElem}
	
	subsort CabsLoc < C
	subsort TypeSpecifier < C
	subsort Storage < C
	--- subsort FunSpecifier < C
	subsort CVSpecifier < C
	subsort SpecifierElem < C
	subsort Specifier < C
	subsort DeclType < C
	subsort NameGroup < C
	subsort FieldGroup < C
	subsort InitNameGroup < C
	subsort Name < C
	subsort InitName < C
	subsort SingleName < C
	subsort EnumItem < C
	subsort Definition < C
	subsort Block < C
	subsort AsmDetails < C
	subsort Statement < C
	subsort PureStatement < C
	subsort PureEnumItem < C
	subsort ForClause < C
	--- subsort BinaryOperator < C
	--- subsort UnaryOperator < C
	subsort Expression < C
	subsort Constant < C
	subsort InitExpression < C
	subsort InitWhat < C
	subsort Attribute < C
	subsort Program < C
	subsort TranslationUnit < C
	subsort IntConstant < C
	subsort InitFragment < C
	subsort FieldName < C
	subsort PureDefinition < C

--- -----------------------------------------------------------------------------
--- Below, I give the declaration as found in cabs.ml first, followed by the K version
	
***(
type cabsloc = {
		lineno : int;
		filename: string;
		byteno: int;
		ident : int;
	}
***)
	op CabsLoc : String Int Int Int -> CabsLoc
	
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
***)
	ops Void Char Bool Short Int Long Float Double Signed Unsigned : -> TypeSpecifier [ctor]
	op Named : Id -> TypeSpecifier [ctor]
***(
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
***)	
	op StructRef : Id -> TypeSpecifier [ctor] --- new
	op StructDef : Id List{C} -> TypeSpecifier [strict(2) ctor] --- new
	op UnionRef : Id -> TypeSpecifier [ctor] --- new
	op UnionDef : Id List{C} -> TypeSpecifier [strict(2) ctor] --- new
	op EnumRef : Id -> TypeSpecifier [ctor] --- new
	op EnumDef : Id List{C} -> TypeSpecifier [strict(2) ctor] --- new
	op TypeofExpression : K -> TypeSpecifier [ctor]
	op TypeofType : K K -> TypeSpecifier [ctor]

***(
and storage =
	NO_STORAGE | AUTO | STATIC | EXTERN | REGISTER
***)
	ops NoStorage Auto Static Extern Register : -> Storage [ctor]
	
***(
and funspec = 
	INLINE | VIRTUAL | EXPLICIT
***)
	--- Not sure what this is from, maybe C++?  It's not used elsewhere in cabs.
	
***(
and cvspec =
	CV_CONST | CV_VOLATILE | CV_RESTRICT
***)
	ops Const Volatile Restrict : -> CVSpecifier
	
***(
and spec_elem =
	SpecTypedef          
	| SpecCV of cvspec            (* const/volatile *)
	| SpecAttr of attribute       (* __attribute__ *)
	| SpecStorage of storage
	| SpecInline
	| SpecType of typeSpecifier
	| SpecPattern of string       (* specifier pattern variable *)
***)
	op SpecTypedef : -> SpecifierElem
	--- the following are because I flattened SpecifierElem
	subsort CVSpecifier < SpecifierElem
	--- subsort Attribute < SpecifierElem
	subsort Storage < SpecifierElem
	op Inline : -> SpecifierElem
	subsort TypeSpecifier < SpecifierElem
	op SpecPattern : Id -> SpecifierElem
	
***(
	and specifier = spec_elem list
***)
	op Specifier : List{C} -> Specifier [strict]
	
***(
and decl_type =
	| JUSTBASE		(* Prints the declared name *)
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
			(* Prints "decl (args[, ...])".
			 * decl is never a PTR.*)
***)
	op JustBase : -> K
	op FunctionType : K -> DeclType [strict]
	op ArrayType : K K -> DeclType [strict(1 2)]
	op PointerType : K -> DeclType [strict]
	op Prototype : K List{C} Bool -> DeclType [strict(1 2)]
	
	
***(
and name_group = specifier * name list
***)
	op NameGroup : K List{C} -> NameGroup [strict(1 2)]
	
***(
	(* The optional expression is the bitfield *)
and field_group = specifier * (name * expression option) list
***)
	op FieldGroup : K List{C} -> FieldGroup [strict(1)]
	op FieldName : K -> FieldName --- new
	op BitFieldName : K K -> FieldName --- new
	
***(
	(* like name_group, except the declared variables are allowed to have initializers *)
	(* e.g.: int x=1, y=2; *)
and init_name_group = specifier * init_name list
***)
	op InitNameGroup : K List{C} -> InitNameGroup [strict(1)]
	
***(
	(* The decl_type is in the order in which they are printed. Only the name of
	 * the declared identifier is pulled out. The attributes are those that are
	 * printed after the declarator *)
	(* e.g: in "int *x", "*x" is the declarator; "x" will be pulled out as *)
	(* the string, and decl_type will be PTR([], JUSTBASE) *)
and name = string * decl_type * attribute list * cabsloc
***)
	op Name : Id K -> Name
	op #NoName : -> Id --- new
	op Identifier : String -> Id --- new	
	op NameLoc : K K -> Name --- new
***(
	(* A variable declarator ("name") with an initializer *)
and init_name = name * init_expression
***)
	op InitName : K K -> InitName [strict(2)]
	
***(
	(* Single names are for declarations that cannot come in groups, like
	 * function parameters and functions *)
and single_name = specifier * name
***)
	op SingleName : K K -> SingleName [strict(1)]
	
***(
and enum_item = string * expression * cabsloc
***)
	op EnumItem : Id K -> PureEnumItem [strict(2)]
	op EnumItemLoc : K K -> EnumItem --- new
		
***(
	(*
	** Declaration definition (at toplevel)
	*)
	and definition =
	   FUNDEF of single_name * block * cabsloc * cabsloc
	 | DECDEF of init_name_group * cabsloc        (* variable(s), or function prototype *)
	 | TYPEDEF of name_group * cabsloc
	 | ONLYTYPEDEF of specifier * cabsloc
	 | GLOBASM of string * cabsloc
	 | PRAGMA of expression * cabsloc
	 | LINKAGE of string * cabsloc * definition list (* extern "C" { ... } *)
	 (* toplevel form transformer, from the first definition to the *)
	 (* second group of definitions *)
	 | TRANSFORMER of definition * definition list * cabsloc
	 (* expression transformer: source and destination *)
	 | EXPRTRANSFORMER of expression * expression * cabsloc
***)
	op FunctionDefinition : K K -> PureDefinition [strict(1)]
	op DeclarationDefinition : K -> PureDefinition
	op Typedef : K -> PureDefinition
	op OnlyTypedef : K -> PureDefinition [strict]
	op GlobAsm : String -> PureDefinition
	op Pragma : K -> PureDefinition
	op Linkage : String List{C} -> PureDefinition
	op Transformer : K List{C} -> PureDefinition
	op ExpressionTransformer : K K -> PureDefinition
	
	op DefinitionLoc : K K -> Definition --- new
	op DefinitionLocRange : K K K -> Definition --- new

***(
(* the string is a file name, and then the list of toplevel forms *)
and file = string * definition list
***)
	--- name, code, source
	op TranslationUnit : String List{C} String -> TranslationUnit --- new
	op Program : List{C} -> Program --- new

***(
	(* A block contains a list of local label declarations ( GCC's ({ __label__ 
	 * l1, l2; ... }) ) , a list of definitions and a list of statements  *)
and block = 
	{ blabels: string list;
	  battrs: attribute list;
	  bstmts: statement list
	} 
***)
	op Block : List{C} List{C} -> Block
	
***(
	(* GCC asm directives have lots of extra information to guide the optimizer *)
and asm_details =
	{ aoutputs: (string option * string * expression) list; 
	(* optional name, constraints and expressions for outputs *)
	ainputs: (string option * string * expression) list; 
	(* optional name, constraints and expressions for inputs *)
	aclobbers: string list 
	(* clobbered registers *)
	}
***)
	--- TODO

***(
and statement =
	NOP of cabsloc
	| COMPUTATION of expression * cabsloc
	| BLOCK of block * cabsloc
	| SEQUENCE of statement * statement * cabsloc
***)
	op Nop : -> PureStatement
	op Computation : K -> PureStatement
	op BlockStatement : K -> PureStatement
	op Sequence : K K -> PureStatement
***(
	| IF of expression * statement * statement * cabsloc
	| WHILE of expression * statement * cabsloc
	| DOWHILE of expression * statement * cabsloc
	| FOR of for_clause * expression * expression * statement * cabsloc
***)
	op IfThenElse : K K K -> PureStatement [strict(1)] 
	op While : K K -> PureStatement
	op DoWhile : K K -> PureStatement
	op For : K K K K -> PureStatement
***(
	| BREAK of cabsloc
	| CONTINUE of cabsloc
	| RETURN of expression * cabsloc
***)
	op Break : -> PureStatement
	op Continue : -> PureStatement
	op Return : K -> PureStatement [strict]
***(
	| SWITCH of expression * statement * cabsloc
	| CASE of expression * statement * cabsloc
	| CASERANGE of expression * expression * statement * cabsloc
	| DEFAULT of statement * cabsloc
***)
	op Switch : K K -> PureStatement
	op Case : K K -> PureStatement
	op CaseRange : K K K -> PureStatement
	op Default : K -> PureStatement
***(
	| LABEL of string * statement * cabsloc
	| GOTO of string * cabsloc
	| COMPGOTO of expression * cabsloc (* GCC's "goto *exp" *)
	| DEFINITION of definition (*definition or declaration of a variable or type*)
***)
	op Label : Id K -> PureStatement
	op Goto : Id -> PureStatement
	op CompGoto : K -> PureStatement
	op LocalDefinition : K -> PureStatement
***(
	| ASM of attribute list * (* typically only volatile and const *)
		  string list * (* template *)
		  asm_details option * (* extra details to guide GCC's optimizer *)
		  cabsloc
	| TRY_EXCEPT of block * expression * block * cabsloc
	| TRY_FINALLY of block * block * cabsloc
***)
	--- TODO not handling Asm
	op TryExcept : K K K -> PureStatement
	op TryFinally : K K -> PureStatement
	
	--- this wraps all statements with their location in the original file
	op StatementLoc : K K -> Statement --- new
	
***(
and for_clause = 
	FC_EXP of expression
	| FC_DECL of definition
***)
	op ForClauseExpression : K -> ForClause
	op ForClauseDeclaration : K -> ForClause
	
***(
and binary_operator =
	ADD | SUB | MUL | DIV | MOD
	| AND | OR
	| BAND | BOR | XOR | SHL | SHR
	| EQ | NE | LT | GT | LE | GE
	| ASSIGN
	| ADD_ASSIGN | SUB_ASSIGN | MUL_ASSIGN | DIV_ASSIGN | MOD_ASSIGN
	| BAND_ASSIGN | BOR_ASSIGN | XOR_ASSIGN | SHL_ASSIGN | SHR_ASSIGN
  
and expression =
	NOTHING
***)
	op NothingExpression : -> Expression
***(
	| UNARY of unary_operator * expression

and unary_operator =
	MINUS | PLUS | NOT | BNOT | MEMOF | ADDROF
	| PREINCR | PREDECR | POSINCR | POSDECR
***)
	op -_ : K -> Expression [strict prec 22]
	op +_ : K -> Expression [strict prec 22]
	op !_ : K -> Expression [strict prec 22]
	op ~_ : K -> Expression [strict prec 22]
	op *_ : K -> Expression [strict prec 22]
	op &_ : K -> Expression [prec 22]
	op ++_ : K -> Expression [prec 22]
	op --_ : K -> Expression [prec 22]
	op _++ : K -> Expression
	op _-- : K -> Expression

***(
	| LABELADDR of string  (* GCC's && Label *)
***)
	--- TODO not handling && Label
***(
	| BINARY of binary_operator * expression * expression
***)
	ops _*_ _/_ _%_ : K K -> Expression [prec 31 gather(E e) strict]
	ops _+_ _-_ : K K -> Expression [prec 33 gather(E e) strict]
	ops _<<_ : K K -> Expression [prec 35 gather(E e) strict]
	ops _>>_ : K K -> Expression [prec 35 gather(E e) strict]
	ops _<_ _<=_ : K K -> Expression [prec 37 gather(E e) strict]
	ops _>_ _>=_ : K K -> Expression [prec 37 gather(E e) strict]
	ops _==_ _!=_ : K K -> Expression [prec 39 gather(E e) strict]
	op _&_ : K K -> Expression [prec 41 gather(E e) strict]
	op _^_ : K K -> Expression [prec 43 gather(E e) strict]
	op _|_ : K K -> Expression [prec 45 gather(E e) strict]
	op _&&_ : K K -> Expression [prec 47 gather(E e) strict(1)]
	op _||_ : K K -> Expression [prec 49 gather(E e) strict(1)]
	
	ops _*=_ _/=_ _%=_ _+=_ _-=_ _<<=_ _&=_ _^=_ _|=_ : K K -> Expression [prec 53]
	ops _>>=_ : K K -> Expression [prec 53]
	op _:=_ : K K -> Expression [prec 53 strict(2)]
***(
	| QUESTION of expression * expression * expression
***)
	op _?_:_ : K K K -> Expression [strict(1) prec 51 gather(e & E)]
***(
	(* A CAST can actually be a constructor expression *)
	| CAST of (specifier * decl_type) * init_expression
***)
	op Cast : K K K -> Expression [strict(1 3)]
***(
	(* There is a special form of CALL in which the function called is
	   __builtin_va_arg and the second argument is sizeof(T). This 
	   should be printed as just T *)
	| CALL of expression * expression list
***)
	op Call : K List{C} -> Expression [strict]
***(
	| COMMA of expression list
***)
	op Comma : List{C} -> Expression
***(
	| CONSTANT of constant
	| PAREN of expression
	| VARIABLE of string
***)
	op Constant : K -> Expression [strict]
	--- for paren, just putting parentheses
	subsort Id < Expression
***(
	| EXPR_SIZEOF of expression
	| TYPE_SIZEOF of specifier * decl_type
	| EXPR_ALIGNOF of expression
	| TYPE_ALIGNOF of specifier * decl_type
***)
	op SizeofExpression : K -> Expression
	op SizeofType : K K -> Expression [strict(1)]
	op AlignofExpression : K -> Expression
	op AlignofType : K K -> Expression
***(
	| INDEX of expression * expression
***)
	op _`[_`] : K K -> Expression
	--- op ArrayIndex : K K -> Expression
***(
	| MEMBEROF of expression * string
	| MEMBEROFPTR of expression * string
***)
	--- op Dot : K Id -> Expression
	op _._ : K Id -> Expression --- [strict(1)]
	--- op Arrow : K Id -> Expression
	op _->_ : K Id -> Expression [strict(1)]
***(
	| GNU_BODY of block
	| EXPR_PATTERN of string     (* pattern variable, and name *)
***)
	op GnuBody : K -> Expression
	op ExpressionPattern : String -> Expression
	
***(
and constant =
	| CONST_INT of string   (* the textual representation *)
	| CONST_FLOAT of string (* the textual representaton *)
	| CONST_CHAR of int64 list
	| CONST_WCHAR of int64 list
	| CONST_STRING of string
	| CONST_WSTRING of int64 list 
***)
	op DecimalConstant : Int -> IntConstant --- new
	op OctalConstant : K -> IntConstant --- new
	op HexConstant : K -> IntConstant --- new --- expected to be string
	
	op FloatConstant : Float -> IntConstant --- new
	
	op U : K -> Constant --- new
	op L : K -> Constant --- new
	op F : K -> Constant --- new
	op LL : K -> Constant --- new
	op UL : K -> Constant --- new
	op ULL : K -> Constant --- new
	op NoSuffix : K -> Constant --- new
	
	op IntLiteral : K -> Constant
	op FloatLiteral : K -> Constant
	op CharLiteral : Int -> Constant
	op WCharLiteral : Int -> Constant
	op StringLiteral : String -> Constant
	op WStringLiteral : List{C} -> Constant
	

***(
and init_expression =
  | NO_INIT
  | SINGLE_INIT of expression
  | COMPOUND_INIT of (initwhat * init_expression) list
***)
	op NoInit : -> KResult --- InitExpression
	op SingleInit : K -> InitExpression [hybrid strict]
	op CompoundInit : List{C} -> InitExpression [hybrid strict]
	op InitFragment : K K -> InitFragment --- new; (initwhat * init_expression)
	
***(
and initwhat =
	NEXT_INIT
	| INFIELD_INIT of string * initwhat
	| ATINDEX_INIT of expression * initwhat
	| ATINDEXRANGE_INIT of expression * expression
***)
	op NextInit : -> KResult
	op InFieldInit : Id K -> KResult
	op AtIndexInit : K K -> KResult
	op AtIndexRangeInit : K K -> KResult --- nonstandard
	
	
***(
and attribute = string * expression list
***)
	op Attribute : String List{C} -> Attribute

endkm
