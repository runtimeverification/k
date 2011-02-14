open Escape
open Cabs
open Base64
open Big_int

let counter = ref 0
let currentSwitchId = ref 0
let switchStack = ref [0]

let rec trim s =
  let l = String.length s in 
  if l=0 then s
  else if s.[0]=' ' || s.[0]='\t' || s.[0]='\n' || s.[0]='\r' then
    trim (String.sub s 1 (l-1))
  else if s.[l-1]=' ' || s.[l-1]='\t' || s.[l-1]='\n' || s.[l-1]='\r' then
    trim (String.sub s 0 (l-1))
  else
    s


(* this is from cil *)
let escape_char = function
  | '\007' -> "\\a"
  | '\b' -> "\\b"
  | '\t' -> "\\t"
  | '\n' -> "\\n"
  | '\011' -> "\\v"
  | '\012' -> "\\f"
  | '\r' -> "\\r"
  | '"' -> "\\\""
  | '\'' -> "\\'"
  | '\\' -> "\\\\"
  | ' ' .. '~' as printable -> String.make 1 printable
  | unprintable -> Printf.sprintf "\\%03o" (Char.code unprintable)
  
(* this is from cil *)
let escape_string str =
  let length = String.length str in
  let buffer = Buffer.create length in
  for index = 0 to length - 1 do
    Buffer.add_string buffer (escape_char (String.get str index))
  done;
  Buffer.contents buffer

(* Given a character constant (like 'a' or 'abc') as a list of 64-bit
 * values, turn it into a CIL constant.  Multi-character constants are
 * treated as multi-digit numbers with radix given by the bit width of
 * the specified type (either char or wchar_t). *)
(* CME: actually, this is based on the code in CIL *)
let rec reduce_multichar : int64 list -> int64 =
  let radix = 256 in
  List.fold_left
    (fun acc -> Int64.add (Int64.shift_left acc radix))
    Int64.zero
and interpret_character_constant char_list =
  let value = reduce_multichar char_list in
  Int64.to_int value

let replace input output =
    Str.global_replace (Str.regexp_string input) output
(*
<TranslationUnit filename="asdf" source="asdf">
	<FunctionDefinition> </FunctionDefinition>
	<FunctionDefinition> </FunctionDefinition>
	<FunctionDefinition> </FunctionDefinition>
</TranslationUnit>
*)

type attribute =
	Attrib of string * string

(* 
let escapeForXML str =
	(replace "<" "&lt;"
	(replace "\"" "&quot;" str))

let myEscapeChars s = 
	replace "\000" "\\\\0" s
*)
	
(*
let myEscapeChars s = 
	if (String.length s = 0) then "" else (
		(myEscapeChar s.[0]) ^ myEscapeChars
	)
	for i=1 to (String.length s - 1) do 
		if ((Char.code s.[i]) = 0) then (s.[i] <- "\\0") 
	done
*)
	
let cdata (str : string) =
	(* let str = replace "]]>" "]]]]><![CDATA[>" str in *) (* escapes "]]>" *)
	(* let str = replace null "\\0" str in *)
	(* let str = String.escaped str in *)
	"<![CDATA[" ^ str ^ "]]>"

let rec printAttribs (attribs) =
	match attribs with 
		| Attrib (name, data) :: xs -> 
			" " ^ name ^ "=\"" ^ data ^ "\"" ^ printAttribs xs
		| [] -> ""
	
let rec concatN n s =
	if (n = 0) then "" else s ^ (concatN (n-1) s)
	
let printCell (name : string) (attribs) (contents : string) =
	" <" ^ name ^ (printAttribs attribs) ^ ">" ^ contents ^ "</" ^ name ^ "> "
	
let printFlatList f x =
	List.fold_left (fun aux arg -> aux ^ "" ^ (f arg)) "" x

let wrap (d1) (d2) = 	
	printCell d2 [] (printFlatList (fun x -> x) d1)
let printList f x =
	wrap [List.fold_left (fun aux arg -> aux ^ "" ^ (f arg)) "" x] "List"
	
(* this is where the recursive printer starts *)
	
let rec cabsToXML ((filename, defs) : file) (sourceCode : string) = 
(* encoding="utf-8"  *)
	"<?xml version=\"1.1\" encoding=\"utf-8\" ?>\n" ^
	printTranslationUnit filename sourceCode defs
			
and printTranslationUnit (filename : string) (sourceCode : string) defs =
	let filenameCell = (printCell "Filename" [] (printRawString filename)) in	
	wrap (filenameCell :: (printDefs defs) :: (printSource sourceCode) :: []) "TranslationUnit" 
	
and printSource (sourceCode : string) =
	printCell "SourceCode" [] (printRawString sourceCode)
	
and printDefs defs =
	printList printDef defs
	
and printDef def =
	match def with
		| FUNDEF (a, b, c, d) -> 
			printDefinitionLocRange (wrap ((printSingleName a) :: (printBlock b) :: []) "FunctionDefinition") c d
		| DECDEF (a, b) -> 
			printDefinitionLoc (wrap ((printInitNameGroup a) :: []) "DeclarationDefinition") b
		| TYPEDEF (a, b) ->
			printDefinitionLoc (wrap ((printNameGroup a) :: []) "Typedef") b
		| ONLYTYPEDEF (a, b) -> 
			printDefinitionLoc (wrap ((printSpecifier a) :: []) "OnlyTypedef") b
		| GLOBASM (a, b) ->
			printDefinitionLoc (wrap ((printRawString a) :: []) "GlobAsm") b
		| PRAGMA (a, b) ->
			printDefinitionLoc (wrap ((printExpression a) :: []) "Pragma") b
		| LINKAGE (a, b, c) ->
			printDefinitionLoc (wrap ((printRawString a) :: (printDefs c) :: []) "Linkage") b
		| TRANSFORMER (a, b, c) ->
			printDefinitionLoc (wrap ((printDef a) :: (printDefs b) :: []) "Transformer") c
		| EXPRTRANSFORMER (a, b, c) ->
			printDefinitionLoc (wrap ((printExpression a) :: (printExpression b) :: []) "ExprTransformer") c
			
and printDefinitionLoc a l =
	if (hasInformation l) then (wrap (a :: (printCabsLoc l) :: []) "DefinitionLoc") else (a)
and printDefinitionLocRange a b c =
	wrap (a :: (printCabsLoc b) :: (printCabsLoc c) :: []) "DefinitionLocRange"		
and printSingleName (a, b) = 
	wrap ((printSpecifier a) :: (printName b) :: []) "SingleName"
and printAttr a b = wrap (a :: (printAttributeList b) :: []) "AttributeWrapper"
and printBlock a = 
	let blockNum = ((counter := (!counter + 1); !counter)) in
	let blockNumCell = (printRawInt blockNum) in
	let idCell = printCell "BlockId" [] blockNumCell in
	let block = 
	wrap (idCell :: (printBlockLabels a.blabels) :: (printStatementList a.bstmts) :: []) "Block" in
	(* printCell "Block" attribs ((printBlockLabels a.blabels) ^ (printStatementList a.bstmts)) in *)
	printAttr block a.battrs

	(*	
and block = 
    { blabels: string list;
      battrs: attribute list;
      bstmts: statement list
    } *)
and printCabsLoc a = 
	(* let attribs = Attrib ("filename", a.filename )
		:: Attrib ("lineno", string_of_int a.lineno )
		:: Attrib ("byteno", string_of_int a.byteno )
		:: Attrib ("ident", string_of_int a.ident )
		:: []
	in*)
	let contents = 
		(printCell "Filename" [] (printRawString a.filename))
		^ (printCell "Lineno" [] (printRawInt a.lineno))
		^ (printCell "Byteno" [] (printRawInt a.byteno))
		^ (printCell "Ident" [] (printRawInt a.ident)) in
	printCell "CabsLoc" [] contents
(*
type cabsloc = {

 byteno: int;
 ident : int;
}	*)
and hasInformation l =
	l.lineno <> -10
and printNameLoc s l =
	if (hasInformation l) then (wrap (s :: (printCabsLoc l) :: []) "NameLoc") else (s)
and printIdentifier a =
	printCell "Identifier" [] (printRawString a)
and printName (a, b, c, d) = (* string * decl_type * attribute list * cabsloc *)
	if a = "" then 
		printAttr (printNameLoc (wrap ((printDeclType b) :: []) "AnonymousName") d) c
	else 
		printAttr (printNameLoc (wrap ((printIdentifier a) :: (printDeclType b) :: []) "Name") d) c
	
	
and printInitNameGroup (a, b) = 
	wrap ((printSpecifier a) :: (printInitNameList b) :: []) "InitNameGroup"
and printNameGroup (a, b) = 
	wrap ((printSpecifier a) :: (printNameList b) :: []) "NameGroup"
and printNameList a =
	printList printName a
and printInitNameList a = 
	printList printInitName a
and printFieldGroupList a =
	printList printFieldGroup a
and printFieldGroup (spec, fields) =
	wrap ((printSpecifier spec) :: (printFieldList fields) :: []) "FieldGroup"
and printFieldList (fields) =
	printList printField fields
and printField (name, expOpt) =
	match expOpt with
	| None -> wrap ((printName name) :: []) "FieldName"
	| Some exp -> wrap ((printName name) :: (printExpression exp) :: []) "BitFieldName"	
and printInitName (a, b) = 
	wrap ((printName a) :: (printInitExpression b) :: []) "InitName"
and printInitExpression a =
	match a with 
	| NO_INIT -> printCell "NoInit" [] ""
	| SINGLE_INIT exp -> wrap ((printExpression exp) :: []) "SingleInit"
	| COMPOUND_INIT a -> wrap ((printInitFragmentList a) :: []) "CompoundInit"
and printInitExpressionForCast a castPrinter compoundLiteralPrinter = (* this is used when we are printing an init inside a cast, i.e., possibly a compound literal *)
	match a with 
	| NO_INIT -> printCell "Error" [] "cast with a NO_INIT inside doesn't make sense"
	| SINGLE_INIT exp -> castPrinter (printExpression exp)
	| COMPOUND_INIT a -> compoundLiteralPrinter (wrap ((printInitFragmentList a) :: []) "CompoundInit")
and printInitFragmentList a =
	printList printInitFragment a
and printInitFragment (a, b) =
	wrap ((printInitWhat a) :: (printInitExpression b) :: []) "InitFragment"
and printInitWhat a = 
	match a with
	| NEXT_INIT -> printCell "NextInit" [] ""
	| INFIELD_INIT (id, what) -> wrap ((printIdentifier id) :: (printInitWhat what) :: []) "InFieldInit"
	| ATINDEX_INIT (exp, what) -> wrap ((printExpression exp) :: (printInitWhat what) :: []) "AtIndexInit"
	| ATINDEXRANGE_INIT (exp1, exp2) -> wrap ((printExpression exp1) :: (printExpression exp2) :: []) "AtIndexRangeInit"
and printDeclType a =
	printCell "DeclarationType" [] (match a with
	| JUSTBASE -> printCell "JustBase" [] ""
	| PARENTYPE (a, b, c) -> printParenType a b c
	| ARRAY (a, b, c) -> printArrayType a b c
	| PTR (a, b) -> printPointerType a b
	| PROTO (a, b, c) -> printProtoType a b c)
and printParenType a b c =
	printAttr (wrap ((printAttr (printDeclType b) c) :: []) "FunctionType") a
and printArrayType a b c =
	printAttr (wrap ((printDeclType a) :: (printExpression c) :: []) "ArrayType") b
and printPointerType a b =
	printAttr (wrap ((printDeclType b) :: []) "PointerType") a
and printProtoType a b c =
	(* printCell "Prototype" [Attrib ("variadic", string_of_bool c)] (printList (fun x -> x) ((printDeclType a) :: (printSingleNameList b) :: [])) *)
	let variadicName = (if c then "Variadic" else "NotVariadic") in
	let variadicCell = printCell variadicName [] "" in
	wrap ((printDeclType a) :: (printSingleNameList b) :: variadicCell :: []) "Prototype"
and printNop =
	printCell "Nop" [] ""
and printComputation exp =
	wrap ((printExpression exp) :: []) "Computation"
and printExpressionList defs =
	printList printExpression defs
and printBuiltin (sort : string) (data : string) =
	printCell "RawData" [Attrib("sort", sort)] (cdata data)
and printRawString s =
	printBuiltin "String" (Base64.encode_string s)
(* &#38; *)

(* Char ::= #x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] | [#x10000-#x10FFFF] *)
	
and printRawFloat f =
	printRawFloatString (string_of_float f)
and printRawFloatString s =
	printBuiltin "Float" s
and printRawInt i =
	printRawIntString (string_of_int i)
and printRawIntString s =
	printBuiltin "Int" s
(* and printRawInt64 i =
	printBuiltin "Int" (Int64.to_string i) *)
and string_of_list_of_int64 (xs : int64 list) =
	let length = List.length xs in
	let buffer = Buffer.create length in
	let append charcode =
		let addition = String.make 1 (Char.chr (Int64.to_int charcode)) in
		Buffer.add_string buffer addition
	in
	List.iter append xs;
	Buffer.contents buffer
and printConstant const =
	match const with
	| CONST_INT i -> wrap ((printIntLiteral i) :: []) "IntLiteral"
	| CONST_FLOAT r -> wrap ((printFloatLiteral r) :: []) "FloatLiteral"
	| CONST_CHAR c -> wrap [printRawInt (interpret_character_constant c)] "CharLiteral"
	| CONST_WCHAR c -> wrap [printRawInt (interpret_character_constant c)] "WCharLiteral"
	| CONST_STRING s -> wrap [printRawString s] "StringLiteral"
	| CONST_WSTRING ws -> wrap [printRawString (string_of_list_of_int64 ws)] "WStringLiteral"
and splitFloat (xs, i) =
	let lastOne = if (String.length i > 1) then String.uppercase (Str.last_chars i 1) else ("x") in
	let newi = (Str.string_before i (String.length i - 1)) in
	match lastOne with
	| "x" -> (xs, i)
	| "L" -> splitFloat("L" :: xs, newi)
	| "F" -> splitFloat("F" :: xs, newi)
	| _ -> (xs, i)
and splitInt (xs, i) =
	let lastOne = if (String.length i > 1) then String.uppercase (Str.last_chars i 1) else ("x") in
	let newi = (Str.string_before i (String.length i - 1)) in
	match lastOne with
	| "x" -> (xs, i)
	| "U" -> splitInt("U" :: xs, newi)
	| "L" -> splitInt("L" :: xs, newi)
	| _ -> (xs, i)
and printHexFloatConstant f = 
	let significand :: exponentPart :: [] = Str.split (Str.regexp "[pP]") f in
	let wholePart :: fractionalPart = Str.split_delim (Str.regexp "\.") significand in
	let wholePart = (if wholePart = "" then "0" else wholePart) in
	let fractionalPart =
		(match fractionalPart with
		| [] -> "0"
		| "" :: [] -> "0"
		| x :: [] -> x
		) in
	let exponentPart :: [] = Str.split (Str.regexp "[+]") exponentPart in
	let exponentPart = int_of_string exponentPart in
	
	let significand = wholePart ^ "." ^ fractionalPart in
	let approx = float_of_string ("0x" ^ significand) in
	let approx = approx *. (2. ** (float_of_int exponentPart)) in
	let exponentPart = printRawInt exponentPart in
	let significandPart = printRawString significand in
	let significandPart = printCell "Significand" [] significandPart in
	let exponentPart = printCell "Exponent" [] exponentPart in
	let approxPart = printRawFloat approx in
	(wrap (significandPart :: exponentPart :: approxPart :: []) "HexFloatConstant")
	(* let significand = wholePart +. fractionalPart in
	let result = significand *. (2. ** (float_of_int exponentPart)) in
	wrap ((string_of_int (int_of_float wholePart)) :: (string_of_float fractionalPart) :: (string_of_int exponentPart) :: (string_of_float result) :: []) "HexFloatConstant" *)
and printDecFloatConstant f =
	(* print_endline f; *)
	let f = Str.split (Str.regexp "[eE]") f in
	let (significand, exponentPart) = 
		(match f with
		| (x : string) :: [] -> (x, "0")
		| (x : string) :: (y : string) :: [] -> (x, y)
		) in
	let wholePart :: fractionalPart = Str.split_delim (Str.regexp "\.") significand in
	let wholePart = (if wholePart = "" then "0" else wholePart) in
	let fractionalPart =
		(match fractionalPart with
		| [] -> "0"
		| "" :: [] -> "0"
		| x :: [] -> x
		) in
	let stringRep = wholePart ^ "." ^ fractionalPart ^ "e" ^ exponentPart in
	let exponentPart :: [] = Str.split (Str.regexp "[+]") exponentPart in
	let exponentPart = int_of_string exponentPart in
	
	let significand = wholePart ^ "." ^ fractionalPart in
	(* let approx = float_of_string significand in
	let approx = approx *. (10. ** (float_of_int exponentPart)) in *)
	
	let significandPart = printRawString significand in
	let exponentPart = printRawInt exponentPart in
	let approxPart = printRawFloatString stringRep in
	let significandPart = printCell "Significand" [] significandPart in
	let exponentPart = printCell "Exponent" [] exponentPart in
	(wrap (significandPart :: exponentPart :: approxPart :: []) "DecimalFloatConstant")
	
and printFloatLiteral r =
	let (tag, r) = splitFloat ([], r) in
	let num = (
		let firstTwo = if (String.length r > 2) then (Str.first_chars r 2) else ("xx") in
			if (firstTwo = "0x" or firstTwo = "0X") then 
				let nonPrefix = Str.string_after r 2 in
					printHexFloatConstant nonPrefix					
			else ( printDecFloatConstant r)
	) in
	match tag with
	| "F" :: [] -> wrap (num :: []) "F"
	| "L" :: [] -> wrap (num :: []) "L"
	| [] -> wrap (num :: []) "NoSuffix"
and printHexConstant (i : string) =
	(* let inDec = Int64.of_string ("0x" ^ i) in 
	wrap [printRawInt64 inDec] "HexConstant" *)
	wrap [printRawString i] "HexConstant"
and printOctConstant (i : string) =
	(* let inDec = Int64.of_string ("0o" ^ i) in
	wrap [printRawInt64 inDec] "OctalConstant" *)
	wrap [printRawIntString i] "OctalConstant"
and printDecConstant (i : string) =
	(* let inDec = Int64.of_string i in
	wrap [printRawInt64 inDec] "DecimalConstant" *)
	wrap [printRawIntString i] "DecimalConstant"
and printIntLiteral i =
	let (tag, i) = splitInt ([], i) in
	let num = (
		let firstTwo = if (String.length i > 2) then (Str.first_chars i 2) else ("xx") in
		let firstOne = if (String.length i > 1) then (Str.first_chars i 1) else ("x") in
			if (firstTwo = "0x" or firstTwo = "0X") then 
				printHexConstant (Str.string_after i 2)
			else (if (firstOne = "0") then printOctConstant (Str.string_after i 1) else (printDecConstant i))
	) in
	match tag with
	| "U" :: "L" :: "L" :: []
	| "L" :: "L" :: "U" :: [] -> wrap (num :: []) "ULL"
	| "L" :: "L" :: [] -> wrap (num :: []) "LL"
	| "U" :: "L" :: []
	| "L" :: "U" :: [] -> wrap (num :: []) "UL"
	| "U" :: [] -> wrap (num :: []) "U"
	| "L" :: [] -> wrap (num :: []) "L"
	| [] -> wrap (num :: []) "NoSuffix"
	(* | _ as z -> wrap (num :: []) (List.fold_left (fun aux arg -> aux ^ arg) "" z) *)
	
and printExpression exp =
	match exp with
	| UNARY (op, exp1) -> printUnaryExpression op exp1
	| BINARY (op, exp1, exp2) -> printBinaryExpression op exp1 exp2
	| NOTHING -> printCell "NothingExpression" [] ""
	| PAREN (exp1) -> wrap ((printExpression exp1) :: []) "Paren"
	| LABELADDR (s) -> wrap (s :: []) "GCCLabelOperator"
	| QUESTION (exp1, exp2, exp3) -> wrap ((printExpression exp1) :: (printExpression exp2) :: (printExpression exp3) :: []) "Conditional"
	(* special case below for the compound literals.  i don't know why this isn't in the ast... *)
	| CAST ((spec, declType), initExp) -> 
		let castPrinter x = wrap ((printSpecifier spec) :: (printDeclType declType) :: x :: []) "Cast" in
		let id = (counter := (!counter + 1)); !counter in
		let compoundLiteralIdCell = printCell "CompoundLiteralId" [] (printRawInt id) in
		let compoundLiteralPrinter x = wrap (compoundLiteralIdCell :: (printSpecifier spec) :: (printDeclType declType) :: x :: []) "CompoundLiteral"
		in printInitExpressionForCast initExp castPrinter compoundLiteralPrinter
		(* A CAST can actually be a constructor expression *)
	| CALL (exp1, expList) -> wrap ((printExpression exp1) :: (printExpressionList expList) :: []) "Call"
		(* There is a special form of CALL in which the function called is
		__builtin_va_arg and the second argument is sizeof(T). This 
		should be printed as just T *)
	| COMMA (expList) -> wrap ((printExpressionList expList) :: []) "Comma"
	| CONSTANT (const) -> wrap (printConstant const :: []) "Constant"
	| VARIABLE name -> wrap ((printIdentifier name) :: []) "Variable"
	| EXPR_SIZEOF exp1 -> wrap ((printExpression exp1) :: []) "SizeofExpression"
	| TYPE_SIZEOF (spec, declType) -> wrap ((printSpecifier spec) :: (printDeclType declType) :: []) "SizeofType"
	| EXPR_ALIGNOF exp -> wrap ((printExpression exp) :: []) "AlignofExpression"
	| TYPE_ALIGNOF (spec, declType) -> wrap ((printSpecifier spec) :: (printDeclType declType) :: []) "AlignofType"
	| INDEX (exp, idx) -> wrap ((printExpression exp) :: (printExpression idx) :: []) "ArrayIndex"
	| MEMBEROF (exp, fld) -> wrap ((printExpression exp) :: (printIdentifier fld) :: []) "Dot"
	| MEMBEROFPTR (exp, fld) -> wrap ((printExpression exp) :: (printIdentifier fld) :: []) "Arrow"
	| GNU_BODY block -> wrap ((printBlock block) :: []) "GnuBody"
	| EXPR_PATTERN s -> wrap ((printRawString s) :: []) "ExpressionPattern"
and getUnaryOperator op =
	let name = (
	match op with
	| MINUS -> "Negative"
	| PLUS -> "Positive"
	| NOT -> "LogicalNot"
	| BNOT -> "BitwiseNot"
	| MEMOF -> "Dereference"
	| ADDROF -> "Reference"
	| PREINCR -> "PreIncrement"
	| PREDECR -> "PreDecrement"
	| POSINCR -> "PostIncrement"
	| POSDECR -> "PostDecrement"
	) in name
and printUnaryExpression op exp =
	wrap ((printExpression exp) :: []) (getUnaryOperator op)
and printBinaryExpression op exp1 exp2 =
	wrap ((printExpression exp1) :: (printExpression exp2) :: []) (getBinaryOperator op)
	(* wrap ((printBinaryOperator op exp1 exp2) :: []) "BinaryOperator" *)
	(* match op with
	| MUL | DIV | MOD | ADD | SUB
	| SHL | SHR | BAND | XOR | BOR
	| LT | LE | GT | GE | EQ | NE
	| AND | OR -> printBinaryPureOperator op exp1 exp2
	| ASSIGN | ADD_ASSIGN | SUB_ASSIGN | MUL_ASSIGN | DIV_ASSIGN | MOD_ASSIGN 
	| BAND_ASSIGN | BOR_ASSIGN | XOR_ASSIGN | SHL_ASSIGN | SHR_ASSIGN 
		-> printBinaryAssignmentOperator op exp1 exp2 *)
and getBinaryOperator op =
	match op with
	| MUL -> "Multiply"
	| DIV -> "Divide"
	| MOD -> "Modulo"
	| ADD -> "Plus"
	| SUB -> "Minus"
	| SHL -> "LeftShift"
	| SHR -> "RightShift"
	| LT -> "LessThan"
	| LE -> "LessThanOrEqual"
	| GT -> "GreaterThan"
	| GE -> "GreaterThanOrEqual"
	| EQ -> "Equality"
	| NE -> "NotEquality"
	| BAND -> "BitwiseAnd"
	| XOR -> "BitwiseXor"
	| BOR -> "BitwiseOr"
	| AND -> "LogicalAnd"
	| OR -> "LogicalOr"
	| ASSIGN -> "Assign"
	| ADD_ASSIGN -> "AssignPlus"
	| SUB_ASSIGN -> "AssignMinus"
	| MUL_ASSIGN -> "AssignMultiply"
	| DIV_ASSIGN -> "AssignDivide"
	| MOD_ASSIGN -> "AssignModulo"
	| BAND_ASSIGN -> "AssignBitwiseAnd"
	| BOR_ASSIGN -> "AssignBitwiseOr"
	| XOR_ASSIGN -> "AssignBitwiseXor"
	| SHL_ASSIGN -> "AssignLeftShift"
	| SHR_ASSIGN -> "AssignRightShift"
and printSeq _ _ =
	"Seq"
and printIf exp s1 s2 =
	wrap ((printExpression exp) :: (printStatement s1) :: (printStatement s2) :: []) "IfThenElse"
	
and makeBlockStatement stat =
	{ blabels = []; battrs = []; bstmts = stat :: []}
and printWhile exp stat =
	wrap ((printExpression exp) :: (printStatement stat) :: []) "While"
and printDoWhile exp stat =
	wrap ((printExpression exp) :: (printStatement stat) :: []) "DoWhile"
and printFor fc1 exp2 exp3 stat =
	let newForIdCell = printCell "ForId" [] (printRawInt ((counter := (!counter + 1)); !counter)) in
	wrap (newForIdCell :: (printForClause fc1) :: (printExpression exp2) :: (printExpression exp3) :: (printStatement stat) :: []) "For"
and printForClause fc = 
	match fc with
	| FC_EXP exp1 -> wrap ((printExpression exp1) :: []) "ForClauseExpression"
	| FC_DECL dec1 -> wrap ((printDef dec1) :: []) "ForClauseDeclaration"
and printBreak =
	printCell "Break" [] ""
and printContinue =
	printCell "Continue" [] ""
and printReturn exp =
	wrap ((printExpression exp) :: []) "Return"
and printSwitch exp stat =
	let newSwitchId = ((counter := (!counter + 1)); !counter) in
	switchStack := newSwitchId :: !switchStack;
	currentSwitchId := newSwitchId;
	let idCell = printCell "SwitchId" [] (printRawInt newSwitchId) in
	let retval = wrap (idCell :: (printExpression exp) :: (printStatement stat) :: []) "Switch" in
	(* printCell "Switch" [Attrib ("id", string_of_int newSwitchId)] (printList (fun x -> x) ((printExpression exp) :: (printStatement stat) :: [])) in *)
	switchStack := List.tl !switchStack;
	currentSwitchId := List.hd !switchStack;
	retval 
and printCase exp stat =
	let switchIdCell = printCell "SwitchId" [] (printRawInt !currentSwitchId) in
	let caseIdCell = printCell "CaseId" [] (printRawInt (counter := (!counter + 1); !counter)) in
	wrap (switchIdCell :: caseIdCell :: (printExpression exp) :: (printStatement stat) :: []) "Case"
and printCaseRange exp1 exp2 stat =
	wrap ((printExpression exp1) :: (printExpression exp2) :: (printStatement stat) :: []) "CaseRange"
and printDefault stat =
	let switchIdCell = printCell "SwitchId" [] (printRawInt !currentSwitchId) in
	wrap (switchIdCell :: (printStatement stat) :: []) "Default"
and printLabel str stat =
	wrap ((printIdentifier str) :: (printStatement stat) :: []) "Label"	
and printGoto name =
	wrap ((printIdentifier name) :: []) "Goto"
and printCompGoto exp =
	wrap ((printExpression exp) :: []) "CompGoto"
and printBlockStatement block =
	wrap ((printBlock block) :: []) "BlockStatement"
and printStatement a =
	match a with
	| NOP (loc) -> printStatementLoc (printNop) loc
	| COMPUTATION (exp, loc) -> printStatementLoc (printComputation exp) loc
	| BLOCK (blk, loc) -> printStatementLoc (printBlockStatement blk) loc
	| SEQUENCE (s1, s2, loc) -> printStatementLoc (printSeq s1 s2) loc
	| IF (exp, s1, s2, loc) -> printStatementLoc (printIf exp s1 s2) loc
	| WHILE (exp, stat, loc) -> printStatementLoc (printWhile exp stat) loc
	| DOWHILE (exp, stat, loc) -> printStatementLoc (printDoWhile exp stat) loc
	| FOR (fc1, exp2, exp3, stat, loc) -> printStatementLoc (printFor fc1 exp2 exp3 stat) loc
	| BREAK (loc) -> printStatementLoc (printBreak) loc
	| CONTINUE (loc) -> printStatementLoc (printContinue) loc
	| RETURN (exp, loc) -> printStatementLoc (printReturn exp) loc
	| SWITCH (exp, stat, loc) -> printStatementLoc (printSwitch exp stat) loc
	| CASE (exp, stat, loc) -> printStatementLoc (printCase exp stat) loc
	| CASERANGE (exp1, exp2, stat, loc) -> printStatementLoc (printCaseRange exp1 exp2 stat) loc (* GCC's extension *)
	| DEFAULT (stat, loc) -> printStatementLoc (printDefault stat) loc
	| LABEL (str, stat, loc) -> printStatementLoc (printLabel str stat) loc
	| GOTO (name, loc) -> printStatementLoc (printGoto name) loc
	| COMPGOTO (exp, loc) -> printStatementLoc (printCompGoto exp) loc (* GCC's "goto *exp" *)
	| DEFINITION d -> wrap ((printDef d) :: []) "LocalDefinition"
	| _ -> printCell "OtherStatement" [] ""
	(* 
	| ASM (attrs, tlist, details, loc) -> "Assembly" 
	*)
	(* 
	 | TRY_EXCEPT of block * expression * block * cabsloc
	 | TRY_FINALLY of block * block * cabsloc
	*)
and printStatementLoc s l =
	wrap (s :: (printCabsLoc l) :: []) "StatementLoc"
and printStatementList a =
	printList printStatement a
and printAttributeList a =
	printList printAttribute a
and printEnumItemList a =
	printList printEnumItem a
and printBlockLabels a =
	printList (fun x -> x) a
and printAttribute (a, b) =
	wrap ((printRawString a) :: (printExpressionList b) :: []) "Attribute"
and printEnumItem (str, expression, cabsloc) =
	wrap ((wrap ((printIdentifier str) :: (printExpression expression) :: []) "EnumItem") :: (printCabsLoc cabsloc) :: []) "EnumItemLoc"
and printSpecifier a =
	wrap (printSpecElemList a :: []) "Specifier"
and printSpecElemList a =
	printList printSpecElem a
and printSingleNameList a =
	printList printSingleName a
and printSpecElem a =
	match a with
	| SpecTypedef -> printCell "SpecTypedef" [] ""
	| SpecCV cv -> 
		wrap ((match cv with
		| CV_CONST -> printCell "Const" [] ""
		| CV_VOLATILE -> printCell "Volatile" [] ""
		| CV_RESTRICT -> printCell "Restrict" [] "") :: []) "TypeQualifier"
	| SpecAttr al -> printAttribute al
	| SpecStorage sto ->
		wrap ((match sto with
		| NO_STORAGE -> printCell "NoStorage" [] ""
		| AUTO -> printCell "Auto" [] ""
		| STATIC -> printCell "Static" [] ""
		| EXTERN -> printCell "Extern" [] ""
		| REGISTER -> printCell "Register" [] "") :: []) "StorageSpecifier"
	| SpecInline -> (* right now there is only inline, but in C1X there is _Noreturn *)
		wrap ((printCell "Inline" [] "") :: []) "FunctionSpecifier"
	| SpecType bt -> printCell "TypeSpecifier" [] (printTypeSpec bt)
	| SpecPattern name -> wrap ((printIdentifier name) :: []) "SpecPattern"
	
and printTypeSpec = function
	Tvoid -> printCell "Void" [] ""
	| Tchar -> printCell "Char" [] ""
	| Tbool -> printCell "Bool" [] ""
	| Tshort -> printCell "Short" [] ""
	| Tint -> printCell "Int" [] ""
	| Tlong -> printCell "Long" [] ""
	| Tint64 -> printCell "Int64" [] ""
	| Tfloat -> printCell "Float" [] ""
	| Tdouble -> printCell "Double" [] ""
	| Tsigned -> printCell "Signed" [] ""
	| Tunsigned -> printCell "Unsigned" [] ""
	| Tnamed s -> wrap ((printIdentifier s) :: []) "Named"
	| Tstruct (a, b, c) -> printStructType a b c
	| Tunion (a, b, c) -> printUnionType a b c
	| Tenum (a, b, c) -> printEnumType a b c
	| TtypeofE e -> wrap ((printExpression e) :: []) "TypeofExpression"
	| TtypeofT (s, d) -> wrap ((printSpecifier s) :: (printDeclType d) :: []) "TypeofType"
and printStructType a b c =
	printAttr (match b with
		| None -> wrap ((printIdentifier a) :: []) "StructRef"
		| Some b -> wrap ((printIdentifier a) :: (printFieldGroupList b) :: []) "StructDef"
	) c
and printUnionType a b c = 
	printAttr (match b with
		| None -> wrap ((printIdentifier a) :: []) "UnionRef"
		| Some b -> wrap ((printIdentifier a) :: (printFieldGroupList b) :: []) "UnionDef"
	) c
and printEnumType a b c =
	printAttr (match b with
		| None -> wrap ((printIdentifier a) :: []) "EnumRef"
		| Some b -> wrap ((printIdentifier a) :: (printEnumItemList b) :: []) "EnumDef"
	) c




