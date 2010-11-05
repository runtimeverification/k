
open Escape
open Pretty
open Trace
open Cil

module E = Errormsg
module H = Hashtbl
module IH = Inthash
module M = Machdep
module U = Util
module RD = Reachingdefs
module UD = Usedef
module A = Cabs
module CH = Cabshelper
module GA = GrowArray
module RCT = Rmciltmps
module DCE = Deadcodeelim
module EC = Expcompare

let doElimTemps = ref false
let debug = ref false
let printComments = ref false
let envWarnings = ref false

(* Stuff for Deputy support *)
let deputyAttrs = ref false

let thisKeyword = "__this"

type paramkind =
| PKNone
| PKThis
| PKOffset of attrparam

let rec checkParam (ap: attrparam) : paramkind =
  match ap with
  | ACons (name, []) when name = thisKeyword -> PKThis
  | ABinOp (PlusA, a1, a2) when checkParam a1 = PKThis ->
      if a2 = AInt 0 then PKThis else PKOffset a2
  | _ -> PKNone

(* End stuff for Deputy support *)

(* Some(-1) => l1 < l2
   Some(0)  => l1 = l2
   Some(1)  => l1 > l2
   None => different files *)
let loc_comp l1 l2 =
  if String.compare l1.A.filename l2.A.filename != 0
  then None
  else if l1.A.lineno > l2.A.lineno
  then Some(1)
  else if l2.A.lineno > l1.A.lineno
  then Some(-1)
  else if l1.A.byteno > l2.A.byteno
  then Some(1)
  else if l2.A.byteno > l1.A.byteno
  then Some(-1)
  else Some(0)

let simpleGaSearch l =
  let hi = GA.max_init_index CH.commentsGA in
  let rec loop i =
    if i < 0 then -1 else
    let (l',_,_) = GA.get CH.commentsGA i in
    match loc_comp l l' with
      None -> loop (i-1)
    | Some(0) -> i
    | Some(-1) -> loop (i-1)
    | Some(1) -> i
    | _ -> E.s (E.error "simpleGaSearch: unexpected return from loc_comp")
  in
  loop hi

(* location -> string list *)
let get_comments l =
  let cabsl = {A.lineno = l.line; 
	       A.filename = l.file;
	       A.byteno = l.byte;
	       A.ident = 0;} in
  let s = simpleGaSearch cabsl in

  let rec loop i cl =
    if i < 0 then cl else
    let (l',c,b) = GA.get CH.commentsGA i in
    if String.compare cabsl.A.filename l'.A.filename != 0
    then loop (i - 1) cl
    else if b then cl
    else let _ = GA.set CH.commentsGA i (l',c,true) in
    loop (i - 1) (c::cl)
  in
  List.rev (loop s [])

(* clean up some of the mess made below *)
let rec simpl_cond e =
  match e with
  | UnOp(LNot,BinOp(LAnd,e1,e2,t1),t2) ->
      let e1 = simpl_cond (UnOp(LNot,e1,t1)) in
      let e2 = simpl_cond (UnOp(LNot,e2,t1)) in
      BinOp(LOr,e1,e2,t2)
  | UnOp(LNot,BinOp(LOr,e1,e2,t1),t2) ->
      let e1 = simpl_cond (UnOp(LNot,e1,t1)) in
      let e2 = simpl_cond (UnOp(LNot,e2,t1)) in
      BinOp(LAnd,e1,e2,t2)
  | UnOp(LNot,UnOp(LNot,e,_),_) -> simpl_cond e
  | _ -> e

(* the argument b is the body of a Loop *)
(* returns the loop termination condition *)
(* block -> exp option *)
let get_loop_condition b =

  (* returns the first non-empty
   * statement of a statement list *)
  (* stm list -> stm list *)
  let rec skipEmpty = function
    | [] -> []
    | {skind = Instr []; labels = []}::rest ->
	skipEmpty rest
    | x -> x
  in
  (* stm -> exp option * instr list *)
  let rec get_cond_from_if if_stm =
    match if_stm.skind with
      If(e,tb,fb,_) ->
	let e = EC.stripNopCasts e in
	RCT.fold_blocks tb;
	RCT.fold_blocks fb;
	let tsl = skipEmpty tb.bstmts in
	let fsl = skipEmpty fb.bstmts in
	(match tsl, fsl with
	  {skind = Break _} :: _, [] -> Some e
	| [], {skind = Break _} :: _ -> 
	    Some(UnOp(LNot, e, intType))
	| ({skind = If(_,_,_,_)} as s) :: _, [] ->
	    let teo = get_cond_from_if s in
	    (match teo with
	      None -> None
	    | Some te -> 
		Some(BinOp(LAnd,e,EC.stripNopCasts te,intType)))
	| [], ({skind = If(_,_,_,_)} as s) :: _ ->
	    let feo = get_cond_from_if s in
	    (match feo with
	      None -> None
	    | Some fe -> 
		Some(BinOp(LAnd,UnOp(LNot,e,intType),
			   EC.stripNopCasts fe,intType)))
	| {skind = Break _} :: _, ({skind = If(_,_,_,_)} as s):: _ ->
	    let feo = get_cond_from_if s in
	    (match feo with
	      None -> None
	    | Some fe -> 
		Some(BinOp(LOr,e,EC.stripNopCasts fe,intType)))
	| ({skind = If(_,_,_,_)} as s) :: _, {skind = Break _} :: _ ->
	    let teo = get_cond_from_if s in
	    (match teo with
	      None -> None
	    | Some te -> 
		Some(BinOp(LOr,UnOp(LNot,e,intType),
			   EC.stripNopCasts te,intType)))
	| ({skind = If(_,_,_,_)} as ts) :: _ , ({skind = If(_,_,_,_)} as fs) :: _ ->
	    let teo = get_cond_from_if ts in
	    let feo = get_cond_from_if fs in
	    (match teo, feo with
	      Some te, Some fe ->
		Some(BinOp(LOr,BinOp(LAnd,e,EC.stripNopCasts te,intType),
			   BinOp(LAnd,UnOp(LNot,e,intType),
				 EC.stripNopCasts fe,intType),intType))
	    | _,_ -> None)
	| _, _ -> (if !debug then ignore(E.log "cond_finder: branches of %a not good\n"
					   d_stmt if_stm);
		   None))
    | _ -> (if !debug then ignore(E.log "cond_finder: %a not an if\n" d_stmt if_stm);
	    None)
  in
  let sl = skipEmpty b.bstmts in
  match sl with
    ({skind = If(_,_,_,_); labels=[]} as s) :: rest ->
      get_cond_from_if s, rest
  | s :: _ -> 
      (if !debug then ignore(E.log "checkMover: %a is first, not an if\n"
			       d_stmt s);
       None, sl)
  | [] ->
      (if !debug then ignore(E.log "checkMover: no statements in loop block?\n");
       None, sl)


class zraCilPrinterClass : cilPrinter = object (self)
  inherit defaultCilPrinterClass as super

  val genvHtbl : (string, varinfo) H.t = H.create 128
  val lenvHtbl : (string, varinfo) H.t = H.create 128

  (*** VARIABLES ***)

  (* give the varinfo for the variable to be printed,
   * returns the varinfo for the varinfo with that name
   * in the current environment.
   * Returns argument and prints a warning if the variable 
   * isn't in the environment *)
  method private getEnvVi (v:varinfo) : varinfo =
    try
      if H.mem lenvHtbl v.vname
      then H.find lenvHtbl v.vname
      else H.find genvHtbl v.vname
    with Not_found ->
      if !envWarnings then ignore (warn "variable %s not in pp environment" v.vname);
      v

  (* True when v agrees with the entry in the environment for the name of v.
     False otherwise *)
  method private checkVi (v:varinfo) : bool =
    let v' = self#getEnvVi v in
    v.vid = v'.vid

  method private checkViAndWarn (v:varinfo) =
    if not (self#checkVi v) then
      ignore (warn "mentioned variable %s and its entry in the current environment have different varinfo."
		v.vname)


  (** Get the comment out of a location if there is one *)
  method pLineDirective ?(forcefile=false) l =
    let ld = super#pLineDirective l in
    if !printComments then
      let c = String.concat "\n" (get_comments l) in
      match c with
	"" -> ld
      | _ -> ld ++ line ++ text "/*" ++ text c ++ text "*/" ++ line
    else ld

  (* variable use *)
  method pVar (v:varinfo) =
    (* warn about instances where a possibly unintentionally 
       conflicting name is used *)
     if IH.mem RCT.iioh v.vid then
       let rhso = IH.find RCT.iioh v.vid in
       match rhso with
	 Some(Call(_,e,el,l)) ->
	   (* print a call instead of a temp variable *)
	   let oldpit = super#getPrintInstrTerminator() in
	   let _ = super#setPrintInstrTerminator "" in
	   let opc = !printComments in
	   let _ = printComments := false in
	   let c = match unrollType (typeOf e) with
	     TFun(rt,_,_,_) when not (Util.equals (typeSig rt) (typeSig v.vtype)) ->
	       text "(" ++ self#pType None () v.vtype ++ text ")"
	   | _ -> nil in
	   let d = self#pInstr () (Call(None,e,el,l)) in
	   let _ = super#setPrintInstrTerminator oldpit in
	   let _ = printComments := opc in
	   c ++ d
       | _ -> 
	   if IH.mem RCT.incdecHash v.vid then
	     (* print an post-inc/dec instead of a temp variable *)
	     let redefid, rhsvi, b = IH.find RCT.incdecHash v.vid in
	     match b with
	       PlusA | PlusPI | IndexPI ->
		 text rhsvi.vname ++ text "++"
	     | MinusA | MinusPI ->
		 text rhsvi.vname ++ text "--"
	     | _ -> E.s (E.error "zraCilPrinterClass.pVar: unexpected op for inc/dec")
	   else (self#checkViAndWarn v;
		 text v.vname)
     else if IH.mem RCT.incdecHash v.vid then
       (* print an post-inc/dec instead of a temp variable *)
       let redefid, rhsvi, b = IH.find RCT.incdecHash v.vid in
       match b with
	 PlusA | PlusPI | IndexPI ->
	   text rhsvi.vname ++ text "++"
       | MinusA | MinusPI ->
	   text rhsvi.vname ++ text "--"
       | _ -> E.s (E.error "zraCilPrinterClass.pVar: unexpected op for inc/dec")
     else (self#checkViAndWarn v;
	   text v.vname)

 (* variable declaration *)
  method pVDecl () (v:varinfo) =
    (* See if the name is already in the environment with a 
       different varinfo. If so, give a warning.
       If not, add the name to the environment *)
    let _ = if (H.mem lenvHtbl v.vname) && not(self#checkVi v) then
      ignore( warn "name %s has already been declared locally with different varinfo" v.vname)
    else if (H.mem genvHtbl v.vname) && not(self#checkVi v) then
      ignore( warn "name %s has already been declared globally with different varinfo" v.vname)
    else if not v.vglob then
      (if !debug then ignore(E.log "zrapp: adding %s to local pp environment\n" v.vname);
      H.add lenvHtbl v.vname v)
    else
      (if !debug then ignore(E.log "zrapp: adding %s to global pp envirnoment\n" v.vname);
       H.add genvHtbl v.vname v) in
    let stom, rest = separateStorageModifiers v.vattr in
    (* First the storage modifiers *)
    self#pLineDirective v.vdecl ++
    text (if v.vinline then "__inline " else "")
      ++ d_storage () v.vstorage
      ++ (self#pAttrs () stom)
      ++ (self#pType (Some (text v.vname)) () v.vtype)
      ++ text " "
      ++ self#pAttrs () rest

  (* For printing deputy annotations *)
  method pAttr (Attr (an, args) : attribute) : doc * bool =
    if not (!deputyAttrs) then super#pAttr (Attr(an,args)) else
    match an, args with 
    | "fancybounds", [AInt i1; AInt i2] -> nil, false
        (*if !showBounds then
          dprintf "BND(%a, %a)" self#pExp (getBoundsExp i1)
                                self#pExp (getBoundsExp i2), false
        else
          text "BND(...)", false*)
    | "bounds", [a1; a2] ->
        begin
          match checkParam a1, checkParam a2 with
          | PKThis, PKThis ->
              text "COUNT(0)", false
          | PKThis, PKOffset (AInt 1) ->
              text "SAFE", false
          | PKThis, PKOffset a -> nil, false
              (*if !showBounds then
                dprintf "COUNT(%a)" self#pAttrParam a, false
              else
                text "COUNT(...)", false*)
          | _ -> nil, false
             (* if !showBounds then
                dprintf "BND(%a, %a)" self#pAttrParam a1
                                      self#pAttrParam a2, false
              else
                text "BND(...)", false*)
        end
    | "fancysize", [AInt i] -> nil, false
        (*dprintf "SIZE(%a)" self#pExp (getBoundsExp i), false*)
    | "size", [a] ->
        dprintf "SIZE(%a)" self#pAttrParam a, false
    | "fancywhen", [AInt i] -> nil, false
        (*dprintf "WHEN(%a)" self#pExp (getBoundsExp i), false*)
    | "when", [a] ->
        dprintf "WHEN(%a)" self#pAttrParam a, false
    | "nullterm", [] ->
        text "NT", false
    | "assumeconst", [] ->
        text "ASSUMECONST", false
    | "trusted", [] ->
        text "TRUSTED", false
    | "poly", [a] ->
        dprintf "POLY(%a)" self#pAttrParam a, false
    | "poly", [] ->
        text "POLY", false
    | "sentinel", [] ->
        text "SNT", false
    | "nonnull", [] ->
        text "NONNULL", false
    | "_ptrnode", [AInt n] -> nil, false
        (*if !Doptions.emitGraphDetailLevel >= 3 then
          dprintf "NODE(%d)" n, false
        else
          nil, false*)
    | "missing_annot", _->  (* Don't bother printing thess *)
        nil, false
    | _ ->
        super#pAttr (Attr (an, args))
            

  (*** GLOBALS ***)
  method pGlobal () (g:global) : doc =       (* global (vars, types, etc.) *)
    match g with 
    | GFun (fundec, l) ->
        (* If the function has attributes then print a prototype because 
        * GCC cannot accept function attributes in a definition *)
        let oldattr = fundec.svar.vattr in
        (* Always pring the file name before function declarations *)
        let proto = 
          if oldattr <> [] then 
            (self#pLineDirective l) ++ (self#pVDecl () fundec.svar) 
              ++ chr ';' ++ line 
          else nil in
        (* Temporarily remove the function attributes *)
        fundec.svar.vattr <- [];
        let body = (self#pLineDirective ~forcefile:true l) 
                      ++ (self#pFunDecl () fundec) in
        fundec.svar.vattr <- oldattr;
        proto ++ body ++ line
          
    | GType (typ, l) ->
        self#pLineDirective ~forcefile:true l ++
          text "typedef "
          ++ (self#pType (Some (text typ.tname)) () typ.ttype)
          ++ text ";\n"

    | GEnumTag (enum, l) ->
        self#pLineDirective l ++
          text "enum" ++ align ++ text (" " ^ enum.ename) ++
          self#pAttrs () enum.eattr ++ text " {" ++ line
          ++ (docList ~sep:(chr ',' ++ line)
                (fun (n,i, loc) -> 
                  text (n ^ " = ") 
                    ++ self#pExp () i)
                () enum.eitems)
          ++ unalign ++ line ++ text "};\n"

    | GEnumTagDecl (enum, l) -> (* This is a declaration of a tag *)
        self#pLineDirective l ++
          text ("enum " ^ enum.ename ^ ";\n")

    | GCompTag (comp, l) -> (* This is a definition of a tag *)
        let n = comp.cname in
        let su, su1, su2 =
          if comp.cstruct then "struct", "str", "uct"
          else "union",  "uni", "on"
        in
        let sto_mod, rest_attr = separateStorageModifiers comp.cattr in
        self#pLineDirective ~forcefile:true l ++
          text su1 ++ (align ++ text su2 ++ chr ' ' ++ (self#pAttrs () sto_mod)
                         ++ text n
                         ++ text " {" ++ line
                         ++ ((docList ~sep:line (self#pFieldDecl ())) () 
                               comp.cfields)
                         ++ unalign)
          ++ line ++ text "}" ++
          (self#pAttrs () rest_attr) ++ text ";\n"

    | GCompTagDecl (comp, l) -> (* This is a declaration of a tag *)
        self#pLineDirective l ++
          text (compFullName comp) ++ text ";\n"

    | GVar (vi, io, l) ->
        self#pLineDirective ~forcefile:true l ++
          self#pVDecl () vi
          ++ chr ' '
          ++ (match io.init with
            None -> nil
          | Some i -> text " = " ++ 
                (let islong = 
                  match i with
                    CompoundInit (_, il) when List.length il >= 8 -> true
                  | _ -> false 
                in
                if islong then 
                  line ++ self#pLineDirective l ++ text "  " 
                else nil) ++
                (self#pInit () i))
          ++ text ";\n"
      
    (* print global variable 'extern' declarations, and function prototypes *)
    | GVarDecl (vi, l) ->
        let builtins = if !msvcMode then msvcBuiltins else gccBuiltins in
        if not !printCilAsIs && H.mem builtins vi.vname then begin
          (* Compiler builtins need no prototypes. Just print them in
             comments. *)
          text "/* compiler builtin: \n   " ++
            (self#pVDecl () vi)
            ++ text ";  */\n"
          
        end else
          self#pLineDirective l ++
            (self#pVDecl () vi)
            ++ text ";\n"

    | GAsm (s, l) ->
        self#pLineDirective l ++
          text ("__asm__(\"" ^ escape_string s ^ "\");\n")

    | GPragma (Attr(an, args), l) ->
        (* sm: suppress printing pragmas that gcc does not understand *)
        (* assume anything starting with "ccured" is ours *)
        (* also don't print the 'combiner' pragma *)
        (* nor 'cilnoremove' *)
        let suppress =
          not !print_CIL_Input && 
          not !msvcMode &&
          ((startsWith "box" an) ||
           (startsWith "ccured" an) ||
           (an = "merger") ||
           (an = "cilnoremove")) in
        let d =
	  match an, args with
	  | _, [] ->
              text an
	  | "weak", [ACons (symbol, [])] ->
	      text "weak " ++ text symbol
	  | _ ->
            text (an ^ "(")
              ++ docList ~sep:(chr ',') (self#pAttrParam ()) () args
              ++ text ")"
        in
        self#pLineDirective l 
          ++ (if suppress then text "/* " else text "")
          ++ (text "#pragma ")
          ++ d
          ++ (if suppress then text " */\n" else text "\n")

    | GText s  -> 
        if s <> "//" then 
          text s ++ text "\n"
        else
          nil


   method dGlobal (out: out_channel) (g: global) : unit = 
     (* For all except functions and variable with initializers, use the 
      * pGlobal *)
     match g with 
       GFun (fdec, l) -> 
         (* If the function has attributes then print a prototype because 
          * GCC cannot accept function attributes in a definition *)
         let oldattr = fdec.svar.vattr in
         let proto = 
           if oldattr <> [] then 
             (self#pLineDirective l) ++ (self#pVDecl () fdec.svar) 
               ++ chr ';' ++ line
           else nil in
         fprint out 80 (proto ++ (self#pLineDirective ~forcefile:true l));
         (* Temporarily remove the function attributes *)
         fdec.svar.vattr <- [];
         fprint out 80 (self#pFunDecl () fdec);               
         fdec.svar.vattr <- oldattr;
         output_string out "\n"

     | GVar (vi, {init = Some i}, l) -> begin
         fprint out 80 
           (self#pLineDirective ~forcefile:true l ++
              self#pVDecl () vi
              ++ text " = " 
              ++ (let islong = 
                match i with
                  CompoundInit (_, il) when List.length il >= 8 -> true
                | _ -> false 
              in
              if islong then 
                line ++ self#pLineDirective l ++ text "  " 
              else nil)); 
         self#dInit out 3 i;
         output_string out ";\n"
     end

     | g -> fprint out 80 (self#pGlobal () g)

  method pFieldDecl () fi = 
    self#pLineDirective fi.floc ++
    (self#pType
       (Some (text (if fi.fname = missingFieldName then "" else fi.fname)))
       () 
       fi.ftype)
      ++ text " "
      ++ (match fi.fbitfield with None -> nil 
      | Some i -> text ": " ++ num i ++ text " ")
      ++ self#pAttrs () fi.fattr
      ++ text ";"

  method private pFunDecl () f =
    H.add genvHtbl f.svar.vname f.svar;(* add function to global env *)
    H.clear lenvHtbl; (* new local environment *)
    (* add the arguments to the local environment *)
    List.iter (fun vi -> H.add lenvHtbl vi.vname vi) f.sformals;
    let nf = 
      if !doElimTemps
      then RCT.eliminate_temps f
      else f in
    let decls = docList ~sep:line (fun vi -> self#pVDecl () vi ++ text ";")
	() nf.slocals in
    self#pVDecl () nf.svar
      ++  line
      ++ text "{ "
      ++ (align
	    (* locals. *)
	    ++ decls
	    ++ line ++ line
	    (* the body *)
	    ++ ((* remember the declaration *) super#setCurrentFormals nf.sformals; 
          let body = self#pBlock () nf.sbody in
          super#setCurrentFormals [];
          body))
      ++ line
      ++ text "}"

  method private pStmtKind (next : stmt) () (sk : stmtkind) =
    match sk with
    | Loop(b,l,_,_) -> begin
	(* See if we can turn this into a while(e) {} *)
	(* TODO: See if we can turn this into a do { } while(e); *)
	let co, bodystmts = get_loop_condition b in
	match co with
	| None -> super#pStmtKind next () sk
	| Some c -> begin
	    self#pLineDirective l
	      ++ text "wh"
	      ++ (align
		    ++ text "ile ("
		    ++ self#pExp () (simpl_cond (UnOp(LNot,c,intType)))
		    ++ text ") "
		    ++ self#pBlock () {bstmts=bodystmts; battrs=b.battrs})
	end
    end
    | _ -> super#pStmtKind next () sk

end (* class zraCilPrinterClass *)

let zraCilPrinter = new zraCilPrinterClass

(* pretty print an expression *)
let pp_exp (fd : fundec) () (e : exp) =
  deputyAttrs := true;
  ignore(RCT.eliminateTempsForExpPrinting fd);
  let d = zraCilPrinter#pExp () e in
  deputyAttrs := false;
  d

type outfile =
    { fname : string;
      fchan : out_channel }
let outChannel : outfile option ref = ref None

(* Processign of output file arguments *)
let openFile (what: string) (takeit: outfile -> unit) (fl: string) = 
  if !E.verboseFlag then
    ignore (Printf.printf "Setting %s to %s\n" what fl);
  (try takeit {fname = fl; fchan = open_out fl}
  with _ ->
    raise (Arg.Bad ("Cannot open " ^ what ^ " file " ^ fl)))

let feature : featureDescr = 
  { fd_name = "zrapp";              
    fd_enabled = ref false;
    fd_description = "pretty printing with checks for name conflicts and\n\t\t\t\ttemp variable elimination";
    fd_extraopt = [
    "--zrapp_elim_temps",
    Arg.Unit (fun n -> doElimTemps := true),
    "Try to eliminate temporary variables during pretty printing";
    "--zrapp_debug",
    Arg.Unit (fun n -> debug := true; RD.debug := true),
    "Lots of debugging info for pretty printing and reaching definitions";
    "--zrapp_debug_fn",
    Arg.String (fun s -> RD.debug_fn := s),
    "Only output debugging info for one function";
    "--zrapp_comments",
    Arg.Unit (fun _ -> printComments := true),
    "Print comments from source file in output";];
    fd_doit = 
    (function (f: file) -> 
      lineDirectiveStyle := None;
      printerForMaincil := zraCilPrinter);
    fd_post_check = false
  }

