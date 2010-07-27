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
open Cabs
open Escape
(* open Whitetrack *)

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
let rec commas lst = 
	match lst with
		| x::y::xs -> x ^ ", " ^ (commas (y::xs))
		| x::[] -> x
		| [] -> ""
let paren (d)  = "(" ^ d ^ ")"
let parenList l = paren(commas(l))
let wrap (d1) (d2)  = d2 ^ parenList d1
let wrapString d1 d2 = d2 ^ paren(d1)


(*
** FrontC Pretty printer
*)
let out = ref stdout

let printList f x =
	paren (commas (List.map f x))

let printFlatList f x =
	paren (List.fold_left (fun aux arg -> aux ^ " :: " ^ paren (f arg)) "Nil" x)

let rec cabsToString ((fname, defs) : file) = 
	wrapString (printDefs defs) "Program"

and printDefs defs =
	printFlatList printDef defs

and printDef def =
	(match def with
		| FUNDEF (a, b, c, d) -> 
			wrap ((printSingleName a) :: (printBlock b) :: (printCabsLoc c) :: (printCabsLoc d) :: []) "FunDef"
		| DECDEF (a, b) -> 
			wrap ((printInitNameGroup a) :: (printCabsLoc b) :: []) "DecDef"
		| TYPEDEF (a, b) ->
			wrap ((printNameGroup a) :: (printCabsLoc b) :: []) "TypeDef"
		| ONLYTYPEDEF (a, b) -> 
			wrap ((printSpecifier a) :: (printCabsLoc b) :: []) "OnlyTypeDef"
		| GLOBASM (a, b) ->
			wrap (a :: (printCabsLoc b) :: []) "GlobAsm"
		| PRAGMA (a, b) ->
			wrap ((printExp a) :: (printCabsLoc b) :: []) "Pragma"
		| LINKAGE (a, b, c) ->
			wrap (a :: (printCabsLoc b) :: (printDefs c) :: []) "OnlyTypeDef"
		| TRANSFORMER (a, b, c) ->
			wrap ((printDef a) :: (printDefs b) :: (printCabsLoc c) :: []) "Transformer"
		| EXPRTRANSFORMER (a, b, c) ->
			wrap ((printExp a) :: (printExp b) :: (printCabsLoc c) :: []) "ExprTransformer"
		) ^ "\n"
		
and printSingleName (a, b) = 
	wrap ((printSpecifier a) :: (printName b) :: []) "SingleName"
	(* commas ((printSpecifier a) :: (printName b) :: []) *) 
and printBlock a = 
	wrap ((printBlockLabels a.blabels) :: (printAttributeList a.battrs) :: (printStatementList a.bstmts) :: []) "Block"
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
and printIdentifier a =
	wrap (("\"" ^ a ^ "\"") :: []) "Identifier"
and printName (a, b, c, d) = (* string * decl_type * attribute list * cabsloc *)
	wrap ((if a = "" then "#NoName" else (printIdentifier a)) :: (printDeclType b) :: (printAttributeList c) :: (printCabsLoc d) :: []) "Name"
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
and printInitName (a, b) = 
	wrap ((printName a) :: (printInitExpression b) :: []) "InitName"
and printInitExpression a =
	match a with 
	| NO_INIT -> "NoInit"
	| SINGLE_INIT exp -> wrap ((printExp exp) :: []) "SingleInit"
	| COMPOUND_INIT a ->wrap ((printCompoundInit a) :: []) "CompoundInit"
and printCompoundInit a =
	"CompoundInit"
	(* paren (printFlatListWithSep printOneCompoundInit a ", ") *)
and printOneCompoundInit (a, b) =
	"OneCompoundInitTODO"
and printDeclType a =
	match a with
	| JUSTBASE -> "JustBase"
	| PARENTYPE (_, _, _) -> "ParenType"
	| ARRAY (a, b, c) -> printArrayType a b c
	| PTR (a, b) -> printPointerType a b
	| PROTO (a, b, c) -> printProtoType a b c
and printArrayType a b c = 
	"ArrayTODO"
and printPointerType a b = 
	wrap ((printAttributeList a) :: (printDeclType b) :: []) "PointerType"
and printProtoType a b c =
	wrap ((printDeclType a) :: (printSingleNameList b) :: (printBool c) :: []) "Prototype"
and printBool a =
	match a with
	| true -> "true"
	| false -> "false"
and printNop =
	"Nop"
and printComputation exp =
	wrap ((printExp exp) :: []) "Computation"
and printExpList defs = 
	wrap (List.map printExp defs) ""
and printConstant const =
	match const with
	| CONST_INT i -> wrap (i :: []) "Int"
	| CONST_FLOAT r -> wrap (r :: []) "Float"
	| CONST_CHAR c -> wrap (("'" ^ escape_wstring c ^ "'") :: []) "Char"
	| CONST_WCHAR c -> wrap (("L'" ^ escape_wstring c ^ "'") :: []) "WChar"
	| CONST_STRING s -> wrap (s :: []) "String"
	| CONST_WSTRING ws -> wrap (("L\"" ^ escape_wstring ws ^ "\"") :: []) "WString"
and printExp exp =
	match exp with
	| UNARY (op, exp1) -> wrap ((printExp exp1) :: []) (getUnaryOperator op)
	| BINARY (op, exp1, exp2) -> wrap ((printExp exp1) :: (printExp exp2) :: []) (getBinaryOperator op)
	| NOTHING -> "NothingExpression"
	| PAREN (exp1) -> wrap ((printExp exp1) :: []) ""
	| LABELADDR (s) -> wrap (s :: []) "GCCLabelOperator"
	| QUESTION (exp1, exp2, exp3) -> wrap ((printExp exp1) :: (printExp exp2) :: (printExp exp3) :: []) "_?_:_"
	| CAST ((spec, declType), initExp) -> "Cast"
	(* wrap ((printSpec exp1) :: []) "Cast" (* (specifier * decl_type) * init_expression *) *)
		(* A CAST can actually be a constructor expression *)
	| CALL (exp1, expList) -> wrap ((printExp exp1) :: (printExpList expList) :: []) "Apply"
		(* There is a special form of CALL in which the function called is
		__builtin_va_arg and the second argument is sizeof(T). This 
		should be printed as just T *)
	| COMMA (expList) -> wrap ((printExpList expList) :: []) "ExpSeq"
	| CONSTANT (const) -> wrap (printConstant const :: []) "Constant"
	| VARIABLE name -> wrap (name :: []) "Variable"
	| EXPR_SIZEOF exp1 -> wrap ((printExp exp1) :: []) "ExpSizeof"
	| TYPE_SIZEOF (spec, declType) -> "TypeSizeofTODO"
	| EXPR_ALIGNOF exp -> "ExprAlignofTODO"
	| TYPE_ALIGNOF _ -> "TypeAlignofTODO"
	| INDEX (exp, idx) -> "ArrayIndexTODO"
	| MEMBEROF (exp, fld) -> "DotTODO"
	| MEMBEROFPTR (exp, fld) -> "ArrowTODO"
	| GNU_BODY _ -> "GCCBlockExpressionTODO"
	| EXPR_PATTERN _ -> "ExpressionPatternTODO"     (* sm: not sure about this *)
and getUnaryOperator op =
	let name = (
	match op with
	| MINUS -> "-"
	| PLUS -> "+"
	| NOT -> "!"
	| BNOT -> "~"
	| MEMOF -> "*"
	| ADDROF -> "&"
	| PREINCR -> "++"
	| PREDECR -> "--"
	| POSINCR -> "++"
	| POSDECR -> "--"
	) in name ^ "_"
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
and printSeq s1 s2 =
	"Seq"
and printIf exp s1 s2 =
	wrap ((printExp exp) :: (printStatement s1) :: (printStatement s2) :: []) "IfThenElse"
and printWhile exp stat =
	wrap ((printExp exp) :: (printStatement stat) :: []) "While"
and printDoWhile exp stat =
	wrap ((printExp exp) :: (printStatement stat) :: []) "DoWhile"
and printFor fc1 exp2 exp3 stat =
	wrap ((printForClause fc1) :: (printExp exp2) :: (printExp exp3) :: (printStatement stat) :: []) "For"
and printForClause fc = 
	match fc with
	| FC_EXP exp1 -> printExp exp1
	| FC_DECL dec1 -> printDef dec1
and printBreak =
	"Break"
and printContinue =
	"Continue"
and printReturn exp =
	wrap ((printExp exp) :: []) "Return"
and printStatement a =
	match a with
	| NOP (loc) -> printStatementLoc (printNop) loc
	| COMPUTATION (exp, loc) -> printStatementLoc (printComputation exp) loc
	| BLOCK (blk, loc) -> printStatementLoc (printBlock blk) loc
	| SEQUENCE (s1, s2, loc) -> printStatementLoc (printSeq s1 s2) loc
	| IF (exp, s1, s2, loc) -> printStatementLoc (printIf exp s1 s2) loc
	| WHILE (exp, stat, loc) -> printStatementLoc (printWhile exp stat) loc
	| DOWHILE (exp, stat, loc) -> printStatementLoc (printDoWhile exp stat) loc
	| FOR (fc1, exp2, exp3, stat, loc) -> printStatementLoc (printFor fc1 exp2 exp3 stat) loc
	| BREAK (loc) -> printStatementLoc (printBreak) loc
	| CONTINUE (loc) -> printStatementLoc (printContinue) loc
	| RETURN (exp, loc) -> printStatementLoc (printReturn exp) loc
	| _ -> "OtherStatement"
	(* 
	| SWITCH (exp, stat, loc) ->
	setLoc(loc);
	printl ["switch";"("];
	print_expression_level 0 exp;
	print ")";
	print_substatement stat
	| CASE (exp, stat, loc) ->
	setLoc(loc);
	unindent ();
	print "case ";
	print_expression_level 1 exp;
	print ":";
	indent ();
	print_substatement stat
	| CASERANGE (expl, exph, stat, loc) ->
	setLoc(loc);
	unindent ();
	print "case ";
	print_expression expl;
	print " ... ";
	print_expression exph;
	print ":";
	indent ();
	print_substatement stat
	| DEFAULT (stat, loc) ->
	setLoc(loc);
	unindent ();
	print "default :";
	indent ();
	print_substatement stat
	| LABEL (name, stat, loc) ->
	setLoc(loc);
	printl [name;":"];
	space ();
	print_substatement stat
	| GOTO (name, loc) ->
	setLoc(loc);
	printl ["goto";name;";"];
	new_line ()
	| COMPGOTO (exp, loc) -> 
	setLoc(loc);
	print ("goto *"); print_expression exp; print ";"; new_line ()
	| DEFINITION d ->
	print_def d
	| ASM (attrs, tlist, details, loc) ->
	"Assembly" *)
and printStatementLoc s l =
	wrap (s :: (printCabsLoc l) :: []) "StatementLoc"
and printStatementList a =
	match a with 
	| [] -> "NoStatements"
	| x::xs -> printFlatList (fun x -> "\n\t" ^ printStatement x) (x::xs)
and printAttributeList a =
	match a with 
	| [] -> "Nil"
	| x::xs -> printFlatList printAttribute (x::xs)
and printBlockLabels a =
	match a with 
	| [] -> "NoBlockLabels"
	| x::xs -> printFlatList (fun x -> x) (x::xs)
and printAttribute a =
	"Attribute"
and printSpecifier a =
	wrapString (printSpecElemList a) "Specifier"
and printSpecElemList a =
	(* wrapString (parenList (List.map printSpecElem a)) "Specifier" *)
	printFlatList printSpecElem a
and printSingleNameList a =
	(* wrapString (printFlatList printSingleName a) "SingleNameList" *)
	printFlatList printSingleName a
and printSpecElem a =
	match a with
    | SpecTypedef -> "SpecTypedef"
    | SpecInline -> "Inline"
    | SpecStorage sto ->
        (match sto with
        | NO_STORAGE -> "NoStorage"
        | AUTO -> "Auto"
        | STATIC -> "Static"
        | EXTERN -> "Extern"
        | REGISTER -> "Register")
    | SpecCV cv -> 
        (match cv with
        | CV_CONST -> "Const"
        | CV_VOLATILE -> "Volatile"
        | CV_RESTRICT -> "Restrict")
    | SpecAttr al -> "Attribute" (* print_attribute al;*)
    | SpecType bt -> printTypeSpec bt
    (*| SpecPattern name -> printl ["@specifier";"(";name;")"]*)
	| _ -> "UnknownElem"
	
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
	| Tnamed s -> wrap (s :: []) "Named"
	| Tstruct (a, b, c) -> printStructType a b c
	| Tunion (a, b, c) -> printUnionType a b c
	| Tenum (a, b, c) -> printEnumType a b c
	(* | TtypeofE e -> printl ["__typeof__";"("]; print_expression e; print ") "
	| TtypeofT (s,d) -> printl ["__typeof__";"("]; print_onlytype (s, d); print ") " *)
and printStructType a b c =
	"struct"
and printUnionType a b c = 
	"union"
and printEnumType a b c =
	"enum"
	
(* 
and print_def def =
  match def with
    FUNDEF (proto, body, loc, _) ->
      comprint "fundef";
      if !printCounters then begin
        try
          let fname =
            match proto with
              (_, (n, _, _, _)) -> n
          in
          print_def (DECDEF (([SpecType Tint],
                              [(fname ^ "__counter", JUSTBASE, [], cabslu),
                                NO_INIT]), loc));
        with Not_found -> print "/* can't print the counter */"
      end;
      setLoc(loc);
      print_single_name proto;
      print_block body;
      force_new_line ();

  | DECDEF (names, loc) ->
      comprint "decdef";
      setLoc(loc);
      print_init_name_group names;
      print ";";
      new_line ()

  | TYPEDEF (names, loc) ->
      comprint "typedef";
      setLoc(loc);
      print_name_group names;
      print ";";
      new_line ();
      force_new_line ()

  | ONLYTYPEDEF (specs, loc) ->
      comprint "onlytypedef";
      setLoc(loc);
      print_specifiers specs;
      print ";";
      new_line ();
      force_new_line ()

  | GLOBASM (asm, loc) ->
      setLoc(loc);
      printl ["__asm__";"("];  print_string asm; print ");";
      new_line ();
      force_new_line ()

  | PRAGMA (a,loc) ->
      setLoc(loc);
      force_new_line ();
      print "#pragma ";
      let oldwidth = !width in
      width := 1000000;  (* Do not wrap pragmas *)
      print_expression a;
      width := oldwidth;
      force_new_line ()

  | LINKAGE (n, loc, dl) -> 
      setLoc (loc);
      force_new_line ();
      print "extern "; print_string n; print_string "  {";
      List.iter print_def dl;
      print_string "}";
      force_new_line ()

  | TRANSFORMER(srcdef, destdeflist, loc) ->
      setLoc(loc);
      print "@transform {";
      force_new_line();
      print "{";
        force_new_line();
        indent ();
        print_def srcdef;
        unindent();
      print "}";
      force_new_line();
      print "to {";
        force_new_line();
        indent();
        List.iter print_def destdeflist;
        unindent();
      print "}";
      force_new_line()

  | EXPRTRANSFORMER(srcexpr, destexpr, loc) ->
      setLoc(loc);
      print "@transformExpr { ";
      print_expression srcexpr;
      print " } to { ";
      print_expression destexpr;
      print " }";
      force_new_line()
*)