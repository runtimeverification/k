(* 
 *
 * Copyright (c) 2001-2003,
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 *  Ben Liblit          <liblit@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)
(* cprint -- pretty printer of C program from abstract syntax
**
** Project:	FrontC
** File:	cprint.ml
** Version:	2.1e
** Date:	9.1.99
** Author:	Hugues Cassé
**
**	1.0		2.22.99	Hugues Cassé	First version.
**	2.0		3.18.99	Hugues Cassé	Compatible with Frontc 2.1, use of CAML
**									pretty printer.
**	2.1		3.22.99	Hugues Cassé	More efficient custom pretty printer used.
**	2.1a	4.12.99	Hugues Cassé	Correctly handle:
**									char *m, *m, *p; m + (n - p)
**	2.1b	4.15.99	Hugues Cassé	x + (y + z) stays x + (y + z) for
**									keeping computation order.
**	2.1c	7.23.99	Hugues Cassé	Improvement of case and default display.
**	2.1d	8.25.99	Hugues Cassé	Rebuild escape sequences in string and
**									characters.
**	2.1e	9.1.99	Hugues Cassé	Fix, recognize and correctly display '\0'.
*)

(* George Necula: I changed this pretty dramatically since CABS changed *)
open Escape
open Cabs
open XmlPrinter
(* open Whitetrack *)
(*open Xml *)

let version = "Cprint 2.1e 9.1.99 Hugues Cassé"
(*
type loc = { line : int; file : string }

let lu = {line = -1; file = "loc unknown";}
let cabslu = {lineno = -10; 
	      filename = "cabs loc unknown"; 
	      byteno = -10;
              ident = 0;}

let curLoc = ref cabslu

let msvcMode = ref false

let printLn = ref true
let printLnComment = ref false

let printCounters = ref false
let printComments = ref false
*)

let counter = ref 0
let currentSwitchId = ref 0
let switchStack = ref [0]

(* why doesn't this work? *)
(*let counterpp =
	let retval = !counter in
		counter := (retval + 1);
		retval
*)


let rec commas lst = 
	match lst with
		| x::y::xs -> x ^ ", " ^ (commas (y::xs))
		| x::[] -> x
		| [] -> ""
let paren (d)  = "(" ^ d ^ ")"
let parenList l = paren(commas(l))
let wrap (d1) (d2)  = d2 ^ parenList d1
let wrapString d1 d2 = d2 ^ paren(d1)

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

let printFlatList f x =
	paren (List.fold_left (fun aux arg -> aux ^ " :: " ^ paren (f arg)) "Nil" x)

let toString s =
	"\"" ^ (escape_string s) ^ "\""
	
let rec cabsToString ((fname, defs) : file) (fileContents : string) = 
		wrap (("\"" ^ fname ^ "\"") :: (printDefs defs) :: (toString fileContents) :: []) "TranslationUnit"
and cabsToXML ((fname, defs) : file) (fileContents : string) = 
	let ppf = Format.std_formatter in
		IoXML.xprint ppf "@[%a@]@."
			(IoXML.xprint_list xprint_definition) defs; "xml"
(*		wrap (("\"" ^ fname ^ "\"") :: (printDefs defs) :: (toString fileContents) :: []) "TranslationUnit" *)

and printDefs defs =
	printFlatList printDef defs

and printDef def =
	 (match def with
		| FUNDEF (a, b, c, d) -> 
			printDefinitionLocRange (wrap ((printSingleName a) :: (printBlock b) :: []) "FunctionDefinition") c d
		| DECDEF (a, b) -> 
			printDefinitionLoc (wrap ((printInitNameGroup a) :: []) "DeclarationDefinition") b
		| TYPEDEF (a, b) ->
			printDefinitionLoc (wrap ((printNameGroup a) :: []) "Typedef") b
		| ONLYTYPEDEF (a, b) -> 
			printDefinitionLoc (wrap ((printSpecifier a) :: []) "OnlyTypedef") b
		| GLOBASM (a, b) ->
			printDefinitionLoc (wrap (a :: []) "GlobAsm") b
		| PRAGMA (a, b) ->
			printDefinitionLoc (wrap ((printExpression a) :: []) "Pragma") b
		| LINKAGE (a, b, c) ->
			printDefinitionLoc (wrap (a :: (printDefs c) :: []) "Linkage") b
		| TRANSFORMER (a, b, c) ->
			printDefinitionLoc (wrap ((printDef a) :: (printDefs b) :: []) "Transformer") c
		| EXPRTRANSFORMER (a, b, c) ->
			printDefinitionLoc (wrap ((printExpression a) :: (printExpression b) :: []) "ExprTransformer") c
		) ^ "\n"
and printDefinitionLoc a b =
	wrap (a :: (printCabsLoc b) :: []) "DefinitionLoc"
and printDefinitionLocRange a b c =
	wrap (a :: (printCabsLoc b) :: (printCabsLoc c) :: []) "DefinitionLocRange"		
and printSingleName (a, b) = 
	wrap ((printSpecifier a) :: (printName b) :: []) "SingleName"
	(* commas ((printSpecifier a) :: (printName b) :: []) *) 
and printAttr a b = wrap (a :: (printAttributeList b) :: []) "AttributeWrapper"
and printBlock a = 
	printAttr (wrap ((string_of_int (counter := (!counter + 1); !counter)) :: (printBlockLabels a.blabels) :: (printStatementList a.bstmts) :: []) "Block") a.battrs

	(*	
and block = 
    { blabels: string list;
      battrs: attribute list;
      bstmts: statement list
    } *)
and printCabsLoc a = 
	wrap (("\"" ^ a.filename ^ "\"") :: (string_of_int a.lineno) :: (string_of_int a.byteno) :: (string_of_int a.ident) :: []) "CabsLoc"
(*
type cabsloc = {

 byteno: int;
 ident : int;
}	*)
and printNameLoc s l =
	wrap (s :: (printCabsLoc l) :: []) "NameLoc"
and printIdentifier a =
	wrap (("\"" ^ a ^ "\"") :: []) "Identifier"
and printName (a, b, c, d) = (* string * decl_type * attribute list * cabsloc *)
	printAttr (printNameLoc (wrap ((if a = "" then "#NoName" else (printIdentifier a)) :: (printDeclType b) :: []) "Name") d) c
and printInitNameGroup (a, b) = 
	wrap ((printSpecifier a) :: (printInitNameList b) :: []) "InitNameGroup"
and printNameGroup (a, b) = 
	wrap ((printSpecifier a) :: (printNameList b) :: []) "NameGroup"
and printNameList a =
	(* wrap ((paren (commas (List.map printName a))) :: []) "NameList" *)
	(* paren (commas (List.map printName a)) *)
	printFlatList printName a
and printInitNameList a = 
	(* wrap ((paren (commas (List.map printInitName a))) :: []) "InitNameList" *)
	(* (paren (commas (List.map printInitName a))) *)
	printFlatList printInitName a
and printFieldGroupList a =
	printFlatList printFieldGroup a
and printFieldGroup (spec, fields) =
	wrap ((printSpecifier spec) :: (printFieldList fields) :: []) "FieldGroup"
and printFieldList (fields) =
	printFlatList printField fields
and printField (name, expOpt) =
	match expOpt with
	| None -> wrap ((printName name) :: []) "FieldName"
	| Some exp -> wrap ((printName name) :: (printExpression exp) :: []) "BitFieldName"	
and printInitName (a, b) = 
	wrap ((printName a) :: (printInitExpression b) :: []) "InitName"
and printInitExpression a =
	match a with 
	| NO_INIT -> "NoInit"
	| SINGLE_INIT exp -> wrap ((printExpression exp) :: []) "SingleInit"
	| COMPOUND_INIT a -> wrap ((printInitFragmentList a) :: []) "CompoundInit"
and printInitExpressionForCast a castPrinter compoundLiteralPrinter = (* this is used when we are printing an init inside a cast, i.e., possibly a compound literal *)
	match a with 
	| NO_INIT -> "Error(\"cast with a NO_INIT inside doesn't make sense\")"
	| SINGLE_INIT exp -> castPrinter (printExpression exp)
	| COMPOUND_INIT a -> compoundLiteralPrinter (wrap ((printInitFragmentList a) :: []) "CompoundInit")
and printInitFragmentList a =
	printFlatList printInitFragment a
and printInitFragment (a, b) =
	wrap ((printInitWhat a) :: (printInitExpression b) :: []) "InitFragment"
and printInitWhat a = 
	match a with
	| NEXT_INIT -> "NextInit"
	| INFIELD_INIT (id, what) -> wrap ((printIdentifier id) :: (printInitWhat what) :: []) "InFieldInit"
	| ATINDEX_INIT (exp, what) -> wrap ((printExpression exp) :: (printInitWhat what) :: []) "AtIndexInit"
	| ATINDEXRANGE_INIT (exp1, exp2) -> wrap ((printExpression exp1) :: (printExpression exp2) :: []) "AtIndexRangeInit"
and printDeclType a =
	match a with
	| JUSTBASE -> "JustBase"
	| PARENTYPE (a, b, c) -> printParenType a b c
	| ARRAY (a, b, c) -> printArrayType a b c
	| PTR (a, b) -> printPointerType a b
	| PROTO (a, b, c) -> printProtoType a b c
and printParenType a b c =
	printAttr (wrap ((printAttr (printDeclType b) c) :: []) "FunctionType") a
and printArrayType a b c =
	printAttr (wrap ((printDeclType a) :: (printExpression c) :: []) "ArrayType") b
and printPointerType a b =
	printAttr (wrap ((printDeclType b) :: []) "PointerType") a
and printProtoType a b c =
	wrap ((printDeclType a) :: (printSingleNameList b) :: (printBool c) :: []) "Prototype"
and printBool a =
	match a with
	| true -> "true"
	| false -> "false"
and printNop =
	"Nop"
and printComputation exp =
	wrap ((printExpression exp) :: []) "Computation"
and printExpressionList defs = 
	(* wrap (List.map printExpression defs) "" *)
	printFlatList printExpression defs
and printConstant const =
	match const with
	| CONST_INT i -> wrap ((printIntLiteral i) :: []) "IntLiteral"
	| CONST_FLOAT r -> wrap ((printFloatLiteral r) :: []) "FloatLiteral"
	| CONST_CHAR c -> wrap ((string_of_int (interpret_character_constant c)) :: []) "CharLiteral"
	| CONST_WCHAR c -> wrap ((string_of_int (interpret_character_constant c)) :: []) "WCharLiteral"
	| CONST_STRING s -> wrap (("\"" ^ escape_string s ^ "\"") :: []) "StringLiteral"
	| CONST_WSTRING ws -> wrap (("\"" ^ escape_wstring ws ^ "\"") :: []) "WStringLiteral"
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
and printHexFloat f = 
	let significand :: exponent :: [] = Str.split (Str.regexp "[pP]") f in
	let wholeSignificand :: fractionalSignificand = Str.split_delim (Str.regexp "\.") significand in
	let wholeSignificand = (if wholeSignificand = "" then "0" else wholeSignificand) in
	let fractionalSignificand =
		(match fractionalSignificand with
		| [] -> "0"
		| "" :: [] -> "0"
		| x :: [] -> x
		) in
	let exponent :: [] = Str.split (Str.regexp "[+]") exponent in
	let exponent = int_of_string exponent in
	let wholeSignificand = float_of_string ("0x" ^ wholeSignificand) in
	let fractionalSignificand = float_of_string ("0x." ^ fractionalSignificand) in
	let significand = wholeSignificand +. fractionalSignificand in
	let result = significand *. (2. ** (float_of_int exponent)) in
	wrap ((string_of_int (int_of_float wholeSignificand)) :: (string_of_float fractionalSignificand) :: (string_of_int exponent) :: (string_of_float result) :: []) "HexFloatConstant"
	(* (wrapString ("\"" ^ f ^ "\"") "HexFloatConstant") *)
and printFloatLiteral r =
	let (tag, r) = splitFloat ([], r) in
	let num = (
		let firstTwo = if (String.length r > 2) then (Str.first_chars r 2) else ("xx") in
			if (firstTwo = "0x" or firstTwo = "0X") then 
				let nonPrefix = Str.string_after r 2 in
					printHexFloat nonPrefix					
			else (
				(wrapString r "DecimalFloatConstant")
			)
	) in
	match tag with
	| "F" :: [] -> wrapString num "F"
	| "L" :: [] -> wrapString num "L"
	| [] -> wrapString num "NoSuffix"
and printIntLiteral i =
	let (tag, i) = splitInt ([], i) in
	let num = (
		let firstTwo = if (String.length i > 2) then (Str.first_chars i 2) else ("xx") in
		let firstOne = if (String.length i > 1) then (Str.first_chars i 1) else ("x") in
			if (firstTwo = "0x" or firstTwo = "0X") then 
				(wrapString ("\"" ^ Str.string_after i 2 ^ "\"") "HexConstant")
			else (
				if (firstOne = "0") then
					(wrapString (Str.string_after i 1) "OctalConstant")
				else (
					wrapString i "DecimalConstant"
				)
			)
	) in
	match tag with
	| "U" :: "L" :: "L" :: []
	| "L" :: "L" :: "U" :: [] -> wrapString num "ULL"
	| "L" :: "L" :: [] -> wrapString num "LL"
	| "U" :: "L" :: []
	| "L" :: "U" :: [] -> wrapString num "UL"
	| "U" :: [] -> wrapString num "U"
	| "L" :: [] -> wrapString num "L"
	| [] -> wrapString num "NoSuffix"
	(* | _ as z -> wrapString num (List.fold_left (fun aux arg -> aux ^ arg) "" z) *)
	
and printExpression exp =
	match exp with
	| UNARY (op, exp1) -> wrap ((printExpression exp1) :: []) (getUnaryOperator op)
	| BINARY (op, exp1, exp2) -> wrap ((printExpression exp1) :: (printExpression exp2) :: []) (getBinaryOperator op)
	| NOTHING -> "NothingExpression"
	| PAREN (exp1) -> wrap ((printExpression exp1) :: []) ""
	| LABELADDR (s) -> wrap (s :: []) "GCCLabelOperator"
	| QUESTION (exp1, exp2, exp3) -> wrap ((printExpression exp1) :: (printExpression exp2) :: (printExpression exp3) :: []) "_?_:_"
	(* special case below for the compound literals.  i don't know why this isn't in the ast... *)
	| CAST ((spec, declType), initExp) -> 
		let castPrinter x = wrap ((printSpecifier spec) :: (printDeclType declType) :: x :: []) "Cast" in
		let compoundLiteralPrinter x = wrap ((string_of_int ((counter := (!counter + 1)); !counter)) :: (printSpecifier spec) :: (printDeclType declType) :: x :: []) "CompoundLiteral"
		in printInitExpressionForCast initExp castPrinter compoundLiteralPrinter
		(* A CAST can actually be a constructor expression *)
	| CALL (exp1, expList) -> wrap ((printExpression exp1) :: (printExpressionList expList) :: []) "Call"
		(* There is a special form of CALL in which the function called is
		__builtin_va_arg and the second argument is sizeof(T). This 
		should be printed as just T *)
	| COMMA (expList) -> wrap ((printExpressionList expList) :: []) "Comma"
	| CONSTANT (const) -> wrap (printConstant const :: []) "Constant"
	| VARIABLE name -> wrap ((printIdentifier name) :: []) ""
	| EXPR_SIZEOF exp1 -> wrap ((printExpression exp1) :: []) "SizeofExpression"
	| TYPE_SIZEOF (spec, declType) -> wrap ((printSpecifier spec) :: (printDeclType declType) :: []) "SizeofType"
	| EXPR_ALIGNOF exp -> wrap ((printExpression exp) :: []) "AlignofExpression"
	| TYPE_ALIGNOF (spec, declType) -> wrap ((printSpecifier spec) :: (printDeclType declType) :: []) "AlignofType"
	| INDEX (exp, idx) -> wrap ((printExpression exp) :: (printExpression idx) :: []) "_`[_`]"
	| MEMBEROF (exp, fld) -> wrap ((printExpression exp) :: (printIdentifier fld) :: []) "_._"
	| MEMBEROFPTR (exp, fld) -> wrap ((printExpression exp) :: (printIdentifier fld) :: []) "_->_"
	| GNU_BODY block -> wrap ((printBlock block) :: []) "GnuBody"
	| EXPR_PATTERN s -> wrap ((toString s) :: []) "ExpressionPattern"
and getUnaryOperator op =
	let name = (
	match op with
	| MINUS -> "-" ^ "_"
	| PLUS -> "+" ^ "_"
	| NOT -> "!" ^ "_"
	| BNOT -> "~" ^ "_"
	| MEMOF -> "*" ^ "_"
	| ADDROF -> "&" ^ "_"
	| PREINCR -> "++" ^ "_"
	| PREDECR -> "--" ^ "_"
	| POSINCR -> "_" ^ "++"
	| POSDECR -> "_" ^ "--"
	) in name 	
and getBinaryOperator op =
	let name = (
	match op with
	| MUL -> "*"
	| DIV -> "/"
	| MOD -> "%"
	| ADD -> "+"
	| SUB -> "-"
	| SHL -> "<<"
	| SHR -> ">>"
	| LT -> "<"
	| LE -> "<="
	| GT -> ">"
	| GE -> ">="
	| EQ -> "=="
	| NE -> "!="
	| BAND -> "&"
	| XOR -> "^"
	| BOR -> "|"
	| AND -> "&&"
	| OR -> "||"
	| ASSIGN -> ":="
	| ADD_ASSIGN -> "+="
	| SUB_ASSIGN -> "-="
	| MUL_ASSIGN -> "*="
	| DIV_ASSIGN -> "/="
	| MOD_ASSIGN -> "%="
	| BAND_ASSIGN -> "&="
	| BOR_ASSIGN -> "|="
	| XOR_ASSIGN -> "^="
	| SHL_ASSIGN -> "<<="
	| SHR_ASSIGN -> ">>="
	) in "_" ^ name ^ "_"
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
	wrap ((string_of_int ((counter := (!counter + 1)); !counter)) :: (printForClause fc1) :: (printExpression exp2) :: (printExpression exp3) :: (printStatement stat) :: []) "For"
(* these would wrap loop bodies with blocks *)
(* 
and printWhile exp stat =
	wrap ((printExpression exp) :: (printBlockStatement (makeBlockStatement stat)) :: []) "While"
and printDoWhile exp stat =
	wrap ((printExpression exp) :: (printBlockStatement (makeBlockStatement stat)) :: []) "DoWhile"
and printFor fc1 exp2 exp3 stat =
	wrap ((printForClause fc1) :: (printExpression exp2) :: (printExpression exp3) :: (printBlockStatement (makeBlockStatement stat)) :: []) "For"
*)
and printForClause fc = 
	match fc with
	| FC_EXP exp1 -> wrapString (printExpression exp1) "ForClauseExpression"
	| FC_DECL dec1 -> wrapString (printDef dec1) "ForClauseDeclaration"
and printBreak =
	"Break"
and printContinue =
	"Continue"
and printReturn exp =
	wrap ((printExpression exp) :: []) "Return"
and printSwitch exp stat =
	let newSwitchId = ((counter := (!counter + 1)); !counter) in
	switchStack := newSwitchId :: !switchStack;
	currentSwitchId := newSwitchId;
	let retval = wrap ((string_of_int newSwitchId) :: (printExpression exp) :: (printStatement stat) :: []) "Switch" in
	switchStack := List.tl !switchStack;
	currentSwitchId := List.hd !switchStack;
	retval 
(* and printSwitch exp stat =
	let newSwitchId = ((counter := (!counter + 1)); !counter) in
	switchStack := newSwitchId :: !switchStack;
	currentSwitchId := newSwitchId;
	let retval = wrap ((string_of_int newSwitchId) :: (printExpression exp) :: (printBlockStatement (makeBlockStatement stat)) :: []) "Switch" in
	switchStack := List.tl !switchStack;
	currentSwitchId := List.hd !switchStack;
	retval 
*)
and printCase exp stat =
	wrap ((string_of_int !currentSwitchId) :: (string_of_int (counter := (!counter + 1); !counter)) :: (printExpression exp) :: (printStatement stat) :: []) "Case"
and printCaseRange exp1 exp2 stat =
	wrap ((printExpression exp1) :: (printExpression exp2) :: (printStatement stat) :: []) "CaseRange"
and printDefault stat =
	wrap ((string_of_int !currentSwitchId) :: (printStatement stat) :: []) "Default"
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
	| _ -> "OtherStatement"
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
	match a with 
	| [] -> "Nil"
	| x::xs -> printFlatList (fun x -> "\n\t" ^ printStatement x) (x::xs)
and printAttributeList a =
	match a with 
	| [] -> "Nil"
	| x::xs -> printFlatList printAttribute (x::xs)
and printEnumItemList a =
	match a with 
	| [] -> "Nil"
	| x::xs -> printFlatList printEnumItem (x::xs)
and printBlockLabels a =
	match a with 
	| [] -> "Nil"
	| x::xs -> printFlatList (fun x -> x) (x::xs)
and printAttribute (a, b) =
	wrap (("\"" ^ a ^ "\"") :: (printExpressionList b) :: []) "Attribute"
and printEnumItem (str, expression, cabsloc) =
	wrap ((wrap ((printIdentifier str) :: (printExpression expression) :: []) "EnumItem") :: (printCabsLoc cabsloc) :: []) "EnumItemLoc"
and printSpecifier a =
	wrapString (printSpecElemList a) "Specifier"
and printSpecElemList a =
	printFlatList printSpecElem a
and printSingleNameList a =
	printFlatList printSingleName a
and printSpecElem a =
	match a with
	| SpecTypedef -> "SpecTypedef"
	| SpecCV cv -> 
		(match cv with
		| CV_CONST -> "Const"
		| CV_VOLATILE -> "Volatile"
		| CV_RESTRICT -> "Restrict")
	| SpecAttr al -> printAttribute al
	| SpecStorage sto ->
		(match sto with
		| NO_STORAGE -> "NoStorage"
		| AUTO -> "Auto"
		| STATIC -> "Static"
		| EXTERN -> "Extern"
		| REGISTER -> "Register")
	| SpecInline -> "Inline"
	| SpecType bt -> printTypeSpec bt
	| SpecPattern name -> wrap ((printIdentifier name) :: []) "SpecPattern"
	
and printTypeSpec = function
	Tvoid -> "Void"
	| Tchar -> "Char"
	| Tbool -> "Bool"
	| Tshort -> "Short"
	| Tint -> "Int"
	| Tlong -> "Long"
	| Tint64 -> "Int64"
	| Tfloat -> "Float"
	| Tdouble -> "Double"
	| Tsigned -> "Signed"
	| Tunsigned -> "Unsigned"
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
