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
(* let width = ref 80
let tab = ref 2
let max_indent = ref 60

let line = ref ""
let line_len = ref 0
let current = ref ""
let current_len = ref 0
let spaces = ref 0
let follow = ref 0
let roll = ref 0 *)
    


(* stub out the old-style manual space functions *)
(* we may implement some of these later *)
(* let new_line () = print "\n"
let space () = ()
let indent () = ()
let unindent () = ()
let force_new_line () = ()
let flush () = ()
let commit () = () *)

(* sm: for some reason I couldn't just call print from frontc.... ? *)
(* let print_unescaped_string str = print str *)


(*
** Useful primitives
*)
(* 
let print_list print_sep print_elt lst = 
  let _ = List.fold_left
      (fun com elt ->
	if com then print_sep ();
	print_elt elt;
	true)
      false
      lst in
  ()

let print_commas nl fct lst =
  print_list (fun () -> print ","; if nl then new_line() else space()) fct lst
  (* print_maybe "," *)
	
let print_string (s:string) =
  print ("\"" ^ escape_string s ^ "\"")

let print_wstring (s: int64 list ) =
  print ("L\"" ^ escape_wstring s ^ "\"")
*)
(*
** Base Type Printing
*)
(* 
let rec print_specifiers (specs: spec_elem list) =
  comprint "specifier(";
  let print_spec_elem = function
      SpecTypedef -> print "typedef"
    | SpecInline -> printu "inline"
    | SpecStorage sto ->
        printu (match sto with
          NO_STORAGE -> (comstring "/*no storage*/")
        | AUTO -> "auto"
        | STATIC -> "static"
        | EXTERN -> "extern"
        | REGISTER -> "register")
    | SpecCV cv -> 
        printu (match cv with
        | CV_CONST -> "const"
        | CV_VOLATILE -> "volatile"
        | CV_RESTRICT -> "restrict")
    | SpecAttr al -> print_attribute al; space ()
    | SpecType bt -> print_type_spec bt
    | SpecPattern name -> printl ["@specifier";"(";name;")"]
  in
  List.iter print_spec_elem specs
  ;comprint ")"
*)
(*
and print_type_spec = function
    Tvoid -> print "void "
  | Tchar -> print "char "
  | Tbool -> print "_Bool "
  | Tshort -> print "short "
  | Tint -> print "int "
  | Tlong -> print "long "
  | Tint64 -> print "__int64 "
  | Tfloat -> print "float "
  | Tdouble -> print "double "
  | Tsigned -> printu "signed"
  | Tunsigned -> print "unsigned "
  | Tnamed s -> comprint "tnamed"; print s; space ();
  | Tstruct (n, None, _) -> printl ["struct";n]
  | Tstruct (n, Some flds, extraAttrs) ->
      (print_struct_name_attr "struct" n extraAttrs);
      (print_fields flds)
  | Tunion (n, None, _) -> printl ["union";n;" "]
  | Tunion (n, Some flds, extraAttrs) ->
      (print_struct_name_attr "union" n extraAttrs);
      (print_fields flds)
  | Tenum (n, None, _) -> printl ["enum";n]
  | Tenum (n, Some enum_items, extraAttrs) ->
      (print_struct_name_attr "enum" n extraAttrs);
      (print_enum_items enum_items)
  | TtypeofE e -> printl ["__typeof__";"("]; print_expression e; print ") "
  | TtypeofT (s,d) -> printl ["__typeof__";"("]; print_onlytype (s, d); print ") "
*)

(* print "struct foo", but with specified keyword and a list of
 * attributes to put between keyword and name *)
 (*
and print_struct_name_attr (keyword: string) (name: string) (extraAttrs: attribute list) =
begin
  if extraAttrs = [] then
    printl [keyword;name]
  else begin
    print keyword;
    print_attributes extraAttrs;    (* prints a final space *)
    print name;
  end
end
*)

(* This is the main printer for declarations. It is easy bacause the 
 * declarations are laid out as they need to be printed. *)
(* and print_decl (n: string) = 
		comprint "declaration(";
function
    JUSTBASE -> if n <> "___missing_field_name" then 
                  print n
                else
                  comprint "missing field name"
  | PARENTYPE (al1, d, al2) ->
      print "(";
      print_attributes al1; space ();
      print_decl n d; space ();
      print_attributes al2; print ")"
  | PTR (al, d) ->
      print "* ";
      print_attributes al; space ();
      print_decl n d
  | ARRAY (d, al, e) ->
      print_decl n d;
      print "[";
      print_attributes al;
      if e <> NOTHING then print_expression e;
      print "]"
  | PROTO(d, args, isva) ->
      comprint "proto(";
      print_decl n d;
      print "(";
      print_params args isva;
      print ")";
      comprint ")";
	comprint ")";


and print_fields (flds : field_group list) =
  if flds = [] then print " { } "
  else begin
    print " {";
    indent ();
    List.iter
      (fun fld -> print_field_group fld; print ";"; new_line ())
      flds;
    unindent ();
    print "} "
  end

and print_enum_items items =
  if items = [] then print " { } "
  else begin
    print " {";
    indent ();
    print_commas
      true
      (fun (id, exp, loc) -> print id;
	if exp = NOTHING then ()
	else begin
	  space ();
	  print "= ";
	  print_expression exp
	end)
      items;
    unindent ();
    print "} ";
  end

  
and print_onlytype (specs, dt) =
  print_specifiers specs;
  print_decl "" dt
    
and print_name ((n, decl, attrs, _) : name) =
  print_decl n decl;
  space ();
  print_attributes attrs

and print_init_name ((n, i) : init_name) =
  print_name n;
  if i <> NO_INIT then begin
    space ();
    print "= ";
    print_init_expression i
  end
            
and print_name_group (specs, names) =
  print_specifiers specs;
  print_commas false print_name names
    
and print_field_group (specs, fields) =
  print_specifiers specs;
  print_commas false print_field fields
    

and print_field (name, widtho) = 
  print_name name;
  (match widtho with 
    None -> ()
  | Some w -> print " : ";  print_expression w)

and print_init_name_group (specs, names) =
  print_specifiers specs;
  print_commas false print_init_name names
    
and print_single_name (specs, name) =
  print_specifiers specs;
  print_name name

and print_params (pars : single_name list) (ell : bool) =
  print_commas false print_single_name pars;
  if ell then printl (if pars = [] then ["..."] else [",";"..."]) else ()
    
and print_old_params pars ell =
  print_commas false (fun id -> print id) pars;
  if ell then printl (if pars = [] then ["..."] else [",";"..."]) else ()
    *)

(*
** Expression printing
**		Priorities
**		16	variables
**		15	. -> [] call()
**		14  ++, -- (post)
**		13	++ -- (pre) ~ ! - + & *(cast)
**		12	* / %
**		11	+ -
**		10	<< >>
**		9	< <= > >=
**		8	== !=
**		7	&
**		6	^
**		5	|
**		4	&&
**		3	||
**		2	? :
**		1	= ?=
**		0	,				
*)
(*
and get_operator exp =
  match exp with
    NOTHING -> ("", 16)
  | PAREN exp -> ("", 16)
  | UNARY (op, _) ->
      (match op with
	MINUS -> ("-", 13)
      | PLUS -> ("+", 13)
      | NOT -> ("!", 13)
      | BNOT -> ("~", 13)
      | MEMOF -> ("*", 13)
      | ADDROF -> ("&", 13)
      | PREINCR -> ("++", 13)
      | PREDECR -> ("--", 13)
      | POSINCR -> ("++", 14)
      | POSDECR -> ("--", 14))
  | LABELADDR s -> ("", 16)  (* Like a constant *)
  | BINARY (op, _, _) ->
      (match op with
	MUL -> ("*", 12)
      | DIV -> ("/", 12)
      | MOD -> ("%", 12)
      | ADD -> ("+", 11)
      | SUB -> ("-", 11)
      | SHL -> ("<<", 10)
      | SHR -> (">>", 10)
      | LT -> ("<", 9)
      | LE -> ("<=", 9)
      | GT -> (">", 9)
      | GE -> (">=", 9)
      | EQ -> ("==", 8)
      | NE -> ("!=", 8)
      | BAND -> ("&", 7)
      | XOR -> ("^", 6)
      | BOR -> ("|", 5)
      | AND -> ("&&", 4)
      | OR -> ("||", 3)
      | ASSIGN -> ("=", 1)
      | ADD_ASSIGN -> ("+=", 1)
      | SUB_ASSIGN -> ("-=", 1)
      | MUL_ASSIGN -> ("*=", 1)
      | DIV_ASSIGN -> ("/=", 1)
      | MOD_ASSIGN -> ("%=", 1)
      | BAND_ASSIGN -> ("&=", 1)
      | BOR_ASSIGN -> ("|=", 1)
      | XOR_ASSIGN -> ("^=", 1)
      | SHL_ASSIGN -> ("<<=", 1)
      | SHR_ASSIGN -> (">>=", 1))
  | QUESTION _ -> ("", 2)
  | CAST _ -> ("", 13)
  | CALL _ -> ("", 15)
  | COMMA _ -> ("", 0)
  | CONSTANT _ -> ("", 16)
  | VARIABLE name -> ("", 16)
  | EXPR_SIZEOF exp -> ("", 16)
  | TYPE_SIZEOF _ -> ("", 16)
  | EXPR_ALIGNOF exp -> ("", 16)
  | TYPE_ALIGNOF _ -> ("", 16)
  | INDEX (exp, idx) -> ("", 15)
  | MEMBEROF (exp, fld) -> ("", 15)
  | MEMBEROFPTR (exp, fld) -> ("", 15)
  | GNU_BODY _ -> ("", 17)
  | EXPR_PATTERN _ -> ("", 16)     (* sm: not sure about this *)

and print_comma_exps exps =
  print_commas false print_expression exps
    
and print_init_expression (iexp: init_expression) : unit = 
  match iexp with 
    NO_INIT -> ()
  | SINGLE_INIT e -> print_expression e
  | COMPOUND_INIT  initexps ->
      let doinitexp = function
          NEXT_INIT, e -> print_init_expression e
        | i, e -> 
            let rec doinit = function
                NEXT_INIT -> ()
              | INFIELD_INIT (fn, i) -> printl [".";fn]; doinit i
              | ATINDEX_INIT (e, i) -> 
                  print "[";
                  print_expression e;
                  print "]";
                  doinit i
              | ATINDEXRANGE_INIT (s, e) -> 
                  print "["; 
                  print_expression s;
                  print " ... ";
                  print_expression e;
                  print "]"
                in
            doinit i; print " = "; 
            print_init_expression e
      in
      print "{";
      print_commas false doinitexp initexps;
      print "}"
*)
(* and print_expression (exp: expression) = print_expression_level 1 exp *)
(* 
and print_expression_level (lvl: int) (exp : expression) =
  let (txt, lvl') = get_operator exp in
  let _ = match exp with
    NOTHING -> ()
  | PAREN exp -> print "("; print_expression exp; print ")"
  | UNARY (op, exp') ->
      (match op with
	POSINCR | POSDECR ->
	  print_expression_level lvl' exp';
	  print txt
      | _ ->
	  print txt; space (); (* Print the space to avoid --5 *)
	  print_expression_level lvl' exp')
  | LABELADDR l -> printl ["&&";l]
  | BINARY (op, exp1, exp2) ->
			(*if (op = SUB) && (lvl <= lvl') then print "(";*)
      print_expression_level lvl' exp1;
      space ();
      print txt;
      space ();
			(*print_expression exp2 (if op = SUB then (lvl' + 1) else lvl');*)
      print_expression_level (lvl' + 1) exp2 
			(*if (op = SUB) && (lvl <= lvl') then print ")"*)
  | QUESTION (exp1, exp2, exp3) ->
      print_expression_level 2 exp1;
      space ();
      print "? ";
      print_expression_level 2 exp2;
      space ();
      print ": ";
      print_expression_level 2 exp3;
  | CAST (typ, iexp) ->
      print "(";
      print_onlytype typ;
      print ")"; 
     (* Always print parentheses. In a small number of cases when we print 
      * constants we don't need them  *)
      (match iexp with
        SINGLE_INIT e -> print_expression_level 15 e
      | COMPOUND_INIT _ -> (* print "("; *) 
          print_init_expression iexp 
          (* ; print ")" *)
      | NO_INIT -> print "<NO_INIT in cast. Should never arise>")

  | CALL (VARIABLE "__builtin_va_arg", [arg; TYPE_SIZEOF (bt, dt)]) -> 
      comprint "variable";
      print "__builtin_va_arg";
      print "(";
      print_expression_level 1 arg;
      print ",";
      print_onlytype (bt, dt);
      print ")"
  | CALL (exp, args) ->
      print_expression_level 16 exp;
      print "(";
      print_comma_exps args;
      print ")"
  | COMMA exps ->
      print_comma_exps exps
  | CONSTANT cst ->
      (match cst with
	CONST_INT i -> print i
      | CONST_FLOAT r -> print r
      | CONST_CHAR c -> print ("'" ^ escape_wstring c ^ "'")
      | CONST_WCHAR c -> print ("L'" ^ escape_wstring c ^ "'")
      | CONST_STRING s -> print_string s
      | CONST_WSTRING ws -> print_wstring ws)
  | VARIABLE name ->
      comprint "variable";
      print name
  | EXPR_SIZEOF exp ->
      print "sizeof";
      print_expression_level 0 exp
  | TYPE_SIZEOF (bt,dt) ->
      printl ["sizeof";"("];
      print_onlytype (bt, dt);
      print ")"
  | EXPR_ALIGNOF exp ->
      printl ["__alignof__";"("];
      print_expression_level 0 exp;
      print ")"
  | TYPE_ALIGNOF (bt,dt) ->
      printl ["__alignof__";"("];
      print_onlytype (bt, dt);
      print ")"
  | INDEX (exp, idx) ->
      print_expression_level 16 exp;
      print "[";
      print_expression_level 0 idx;
      print "]"
  | MEMBEROF (exp, fld) ->
      print_expression_level 16 exp;
      printl [".";fld]
  | MEMBEROFPTR (exp, fld) ->
      print_expression_level 16 exp;
      printl ["->";fld]
  | GNU_BODY (blk) ->
      print "(";
      print_block blk;
      print ")"
  | EXPR_PATTERN (name) ->
      printl ["@expr";"(";name;")"]
  in
  ()
 *)     
(*
and print_substatement stat =
  match stat with
    IF _
  | SEQUENCE _
  | DOWHILE _ ->
      new_line ();
      print "{";
      indent ();
      print_statement stat;
      unindent ();
      print "}";
      new_line ();
  | BLOCK _ ->
      print_statement stat
  | _ ->
      indent ();
      print_statement stat;
      unindent ()
*)

(*
** GCC Attributes
*)
(*
and print_attribute (name,args) = 
  if args = [] then printu name
  else begin
    print name;
    print "("; if name = "__attribute__" then print "(";
    (match args with
      [VARIABLE "aconst"] -> printu "const"
    | [VARIABLE "restrict"] -> printu "restrict"
    | _ -> print_commas false (fun e -> print_expression e) args);
    print ")"; if name = "__attribute__" then print ")"
  end

(* Print attributes. *)
and print_attributes attrs =
  List.iter (fun a -> print_attribute a; space ()) attrs

(*
** Declaration printing
*)
and print_defs defs =
  let prev = ref false in
  List.iter
    (fun def ->
      (match def with
	DECDEF _ -> prev := false
      | _ ->
	  if not !prev then force_new_line ();
	  prev := true);
      print_def def)
    defs


(* sm: print a comment if the printComments flag is set *)
and comprint (str : string) : unit =
begin
  (* if (!printComments) then (
    print "/*"; *)
    print str;
  (*  print "*/ "
  )
  else
    () *)
end

(* sm: yield either the given string, or "", depending on printComments *)
and comstring (str : string) : string =
begin
  if (!printComments) then
    str
  else
    ""
end
*)

let printListWithSep f x sep =
	List.fold_left (fun aux arg -> aux ^ sep ^ f arg) "" x

let printList f x =
	printListWithSep f x ""

let rec cabsToString ((fname, defs) : file) = 
	printDefs defs

and printDefs defs =
	printList printDef defs

and printDef def =
	(match def with
		(* FUNDEF of single_name * block * cabsloc * cabsloc
		| DECDEF of init_name_group * cabsloc        (* global variable(s), or function prototype *)
		| TYPEDEF of name_group * cabsloc
		| ONLYTYPEDEF of specifier * cabsloc
		| GLOBASM of string * cabsloc
		| PRAGMA of expression * cabsloc
		| LINKAGE of string * cabsloc * definition list (* extern "C" { ... } *)
		(* toplevel form transformer, from the first definition to the *)
		(* second group of definitions *)
		| TRANSFORMER of definition * definition list * cabsloc
		(* expression transformer: source and destination *)
		| EXPRTRANSFORMER of expression * expression * cabsloc *)
		| FUNDEF (a, b, c, d) -> 
			wrap ((printSingleName a) :: (printBlock b) :: (printCabsLoc c) :: (printCabsLoc d) :: []) "FunDef"
		| DECDEF (a, b) -> 
			wrap ((printInitNameGroup a) :: (printCabsLoc b) :: []) "DecDef"
		| _ -> "def")
		^ "\n"
		
and printSingleName (a, b) = 
	(* wrap ((printSpecifier a) :: (printName b) :: []) "SingleName" *)
	commas ((printSpecifier a) :: (printName b) :: [])
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
and printName (a, b, c, d) = (* string * decl_type * attribute list * cabsloc *)
	wrap ((if a = "" then "#No-Name" else a) :: (printDeclType b) :: (printAttributeList c) :: (printCabsLoc d) :: []) "Name"
and printInitNameGroup a = 
	"InitNameGroup"
and printDeclType a =
	match a with
	| JUSTBASE -> "JustBase"
	| PARENTYPE (_, _, _) -> "ParenType"
	| ARRAY (a, b, c) -> printArrayType a b c
	| PTR (a, b) -> printPointerType a b
	| PROTO (a, b, c) -> printProtoType a b c
and printArrayType a b c = 
	"Array"
and printPointerType a b = 
	"Pointer"
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
	| TYPE_SIZEOF (spec, declType) -> "TypeSizeof"
	| EXPR_ALIGNOF exp -> "ExprAlignof"
	| TYPE_ALIGNOF _ -> "TypeAlignof"
	| INDEX (exp, idx) -> "ArrayIndex"
	| MEMBEROF (exp, fld) -> "Dot"
	| MEMBEROFPTR (exp, fld) -> "Arrow"
	| GNU_BODY _ -> "GCCBlockExpression"
	| EXPR_PATTERN _ -> "ExpressionPattern"     (* sm: not sure about this *)
and getUnaryOperator op =
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
and getBinaryOperator op =
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
	| x::xs -> printList (fun x -> "\n\t" ^ printStatement x) (x::xs)
and printAttributeList a =
	match a with 
	| [] -> "NoAttributes"
	| x::xs -> printList printAttribute (x::xs)
and printBlockLabels a =
	match a with 
	| [] -> "NoBlockLabels"
	| x::xs -> printList (fun x -> x) (x::xs)
and printAttribute a =
	"Attribute"
and printSpecifier a =
	printSpecElemList a
and printSpecElemList a =
	wrapString (parenList (List.map printSpecElem a)) "SpecifierList"
and printSingleNameList a =
	printList printSingleName a
and printSpecElem a =
	match a with
    | SpecTypedef -> "typedef"
    | SpecInline -> "inline"
    | SpecStorage sto ->
        (match sto with
        | NO_STORAGE -> "noStorage"
        | AUTO -> "auto"
        | STATIC -> "static"
        | EXTERN -> "extern"
        | REGISTER -> "register")
    | SpecCV cv -> 
        (match cv with
        | CV_CONST -> "const"
        | CV_VOLATILE -> "volatile"
        | CV_RESTRICT -> "restrict")
    | SpecAttr al -> "attribute" (* print_attribute al;*)
    | SpecType bt -> printTypeSpec bt
    (*| SpecPattern name -> printl ["@specifier";"(";name;")"]*)
	| _ -> "unknownElem"
	
and printTypeSpec = function
	Tvoid -> "void "
	| Tchar -> "char "
	| Tbool -> "_Bool "
	| Tshort -> "short "
	| Tint -> "int "
	| Tlong -> "long "
	| Tint64 -> "__int64 "
	| Tfloat -> "float "
	| Tdouble -> "double "
	| Tsigned -> "signed"
	| Tunsigned -> "unsigned "
	| Tnamed s -> wrap (s :: []) "tnamed"
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