(** camlp4 code for generating pretty printers for types, based on the Pretty 
 * module. *)

(*** USAGE ***)
(* To use this module in your code you must add the following line 
 * before the type declarations for which you want to auto generate printing
   functions. 

   let _ = Pretty.auto_printer "ALL"

   If the Pretty module is open, then you can leave the [Pretty.] part out. 
   But you should not do something like P.auto_printer. 

   The scope of the above invocation extends to the end of the module.

   Assume that "foo" and "bar" were declared in the same mutually recursive 
   declaration (occurring after the above auto_printer invocation).
   Then the following functions are generated: 

   let rec d_foo_rec (d_foo: foo -> doc) (d_bar: bar -> doc) : foo -> doc = ...
   and     d_bar_rec (d_foo: foo -> doc) (d_bar: bar -> doc) : bar -> doc = ...
   
   let rec d_foo x = d_foo_rec d_foo d_bar x
   and     d_bar x = d_bar_rec d_foo d_bar x

   let f_foo () = d_foo 
   let f_bar () = d_bar 

   The first set of functions you can use later to override partially the 
   printing function: 

   let rec new_foo = function 
     | A 0 -> text "my special foo"
     | x -> d_foo_rec new_foo new_bar x
   and    new_bar = function 
     | B 1 -> text "my special bar"
     | x -> d_bar_rec new_foo new_bar x

   The second set of functions you can use right away to print, and the f_ 
   functions you can use in conjunction with format strings. 

   An alternative usage mode is to add the following line AFTER each 
   type declaration for which you want printing functions to be 
   generated. 

   let _ = Pretty.auto_printer "foo"

   The above line must occur after the declaration of the type name "foo". 
   Note that you must only mention one of the mutually recursive types when 
   you invoke Pretty.auto_printer, and you get the printing functions for 
   all the types. 


 LIMITATIONS:
   The auto-generated printing functions work for most types. For 
   unrecognized types they will print something of the form <unimplemented>. 
   
   Note that for printing a value of named type "baz", the printer will assume
   that the function d_baz is defined and of the right type. You will get 
   strange messages if this is not the case. 
*)

(**** INSTALATION *******)
(* To use this module you must first compile it and then you must use it 
   as a preprocessor 

   To compile this module add something like this to your Makefile

$(OBJDIR)/pa_prtype.cmo: pa_prtype.ml
	ocamlc -c -pp "camlp4o pa_extend.cmo q_MLast.cmo" \
               -I +camlp4 -I $(OBJDIR) -c $< && \
          mv -f $(<D)/pa_prtype.cmo $@

pa_prtype: $(OBJDIR)/pretty.cmi $(OBJDIR)/pa_prtype.cmo

   And add "pa_prtype" as a first dependency to your target. 

   Note that the dependency generation should work even before you compile 
   the preprocessor. 

   To use this module as a preprocessor you add the following flags to the 
   ocamlc command line:

      -pp "camlp4o -I $(OBJDIR) pa_prtype.cmo"


*******************************************************)


open MLast

open Pretty
module H = Hashtbl

let dogen = ref false

(* The printing function name *)
let p_fun_name (n: string) : string = "d_" ^ n

let p_rec_fun_name (n: string) : string = "d_" ^ n ^ "_rec"

let f_fun_name (n: string) : string = "f_" ^ n

(** We remember the type declarations, in case we see a call to 
 * "auto_printer". *)
let knownTypes: (string, type_decl list) H.t = H.create 13


                                             (* Make a concatenation *)
let rec concatenate (loc: loc) (el: expr list) : expr = 
  match el with 
    [ e ] -> e
  | e1 :: reste -> 
      let restee: expr = concatenate loc reste in 
      <:expr< (Pretty.concat $e1$ $restee$) >>
  | [ ] -> <:expr< Pretty.nil >>
in

(* Make a list with a given separator *)
let rec gen_print_list (loc: loc) (sep: string) (el: expr list) : expr = 
  match el with
    [ e ] -> e
  | e1 :: reste -> 
      let restee: expr = gen_print_list loc sep reste in 
      <:expr< (Pretty.concat
                 (Pretty.concat 
                    (Pretty.concat $e1$ (Pretty.text $str:sep$)) 
                    Pretty.break)
                           $restee$) >>
  | [] -> <:expr< Pretty.nil >>
in

let param_name cnt = "x" ^ string_of_int cnt in

let list_mapi f l =
  let rec loop cnt =
    function
        x :: l -> f cnt x :: loop (cnt + 1) l
      | [] -> []
  in
  loop 1 l
in

let gen_print_cons_patt loc (cons:string) (params: ctyp list) =
  let pl =
    list_mapi (fun n _ -> <:patt< $lid:param_name n$ >>)
      params
  in
  List.fold_left (fun p1 p2 -> <:patt< $p1$ $p2$ >>)
    <:patt< $uid:cons$ >> pl
in

let gen_call loc n f = <:expr< $f$ $lid:param_name n$ >> in


let unimp loc (s: string) = <:expr< Pretty.text $str:s$ >> in
let unimpF loc (s: string) = <:expr< fun _ -> Pretty.text $str:s$ >> in


(* Generate the body of a function that prints a type *)
let rec gen_print_type loc : ctyp -> expr =
  function
    | TyLid (_, s) -> (* named type *)
        if s = "int" then 
          <:expr< Pretty.num >>
        else if s = "string" then
          <:expr< Pretty.text >>
        else if s = "bool" then 
          <:expr< fun b -> if b then Pretty.text "true" else Pretty.text "false"      >>          
        else if s = "int32" then 
          <:expr< Pretty.d_int32 >>
        else if s = "int64" then 
          <:expr< Pretty.d_int64 >>
        else
          <:expr< $lid:p_fun_name s$ >>

    | TyAcc (loc, t1, t2) -> (* Qualified types *) begin
        match t2 with 
          TyLid (_, t2n) -> begin (* Get the module names *)
            let rec getModules = function
                TyUid(loc, m) -> ExUid(loc, m)
              | TyAcc (loc, base, TyUid(locm, m)) -> 
                  ExAcc (loc, getModules base, ExUid (locm, m))
              | _ -> raise Not_found
            in
            try
              (* Look for some special cases *)
              match getModules t1, t2n with 
                ExUid (_, "Pretty"), "doc" -> 
                  <:expr< Pretty.insert () >>
              | _ -> 
                  ExAcc(loc, getModules t1, ExLid (loc, p_fun_name t2n))
            with Not_found -> 
              unimpF loc "TyAcc: path is not TUid"
          end
        | _ -> unimpF loc "TyAcc: t2 is not Lid"
    end

    | TyApp (loc, tcons, tpar) -> begin 
        (* Type constructors *)
        match tcons with 
          TyLid (_, "list") -> 
            <:expr< Pretty.docList $gen_print_type loc tpar$ () >>
        | TyLid (_, "option") -> 
            <:expr< Pretty.docOpt $gen_print_type loc tpar$ () >>

        |  _ -> unimpF loc "TyApp"
    end
          

    | TyTup (loc, typs) -> (* A tuple *)
        (* Make a pattern to match the tuple *)
        let pats: patt list = 
          list_mapi (fun n _ -> <:patt< $lid:param_name n$ >>)
            typs
        in
        let pat: patt = PaTup (loc, pats) in 
        (* The parameters *)
        let pr_params: expr list =
          let type_funs = List.map (gen_print_type loc) typs in
          list_mapi (gen_call loc) type_funs
        in
        (* Put the separators *)
        let sep_params: expr = gen_print_list loc "," pr_params in 
        let e: expr = concatenate loc
            [ <:expr< Pretty.text "(" >> ;
              <:expr< Pretty.align >>;
              <:expr< $sep_params$ >> ;
              <:expr< Pretty.text ")" >> ;
              <:expr< Pretty.unalign >> ]
        in
        <:expr< fun [ $pat$ -> $e$ ] >>

    | TyRec (loc, _, fields) -> (* A record *)
        (* Make a pattern *)
        let pats: (patt * patt) list = 
          list_mapi (fun n (_, fn, _, _) -> 
            <:patt< $lid:fn$ >>, <:patt< $lid:param_name n$ >>)
            fields
        in
        let pat: patt = PaRec (loc, pats) in 
        (* Now print each component *)
        let pr_params: expr list =
          let type_funs = 
            List.map (fun (_, _, _, ft) -> gen_print_type loc ft) fields in
          list_mapi (gen_call loc) type_funs
        in
        (* Put the separators *)
        let sep_params: expr = gen_print_list loc "," pr_params in 
        let e: expr = concatenate loc
            [ <:expr< Pretty.text "{" >> ;
              <:expr< Pretty.align >>;
              <:expr< $sep_params$ >> ;
              <:expr< Pretty.text "}" >> ;
              <:expr< Pretty.unalign >> ]
        in
        <:expr< fun [ $pat$ -> $e$ ] >>
        
    | TySum (loc, _, cdl) -> 
        let gen_print_cons_expr loc (c: string) (tl: ctyp list) : expr =
          let pr_con = <:expr< Pretty.text $str:c$ >> in
          match tl with
            [] -> pr_con
          | _ ->
              (* The parameters *)
              let pr_params: expr list =
                let type_funs = List.map (gen_print_type loc) tl in
                list_mapi (gen_call loc) type_funs
              in
              (* Put the separators *)
              let sep_params: expr = gen_print_list loc "," pr_params in 
              (* Put the alignment two characters into the name of the 
              * constructor *)
              let print_c: expr list = 
                if String.length c > 2 then 
                  let fst = String.sub c 0 2 in 
                  let last = String.sub c 2 (String.length c - 2) in 
                  [ <:expr< Pretty.text $str:fst$ >> ;
                    <:expr< Pretty.align >> ;
                    <:expr< Pretty.text $str:last$ >> ]
                else
                  [ <:expr< Pretty.text $str:c$ >>; 
                    <:expr< Pretty.align >> ]
              in
              let e: expr = concatenate loc
                  (print_c @ [ <:expr< Pretty.text "(" >> ;
                               <:expr< $sep_params$ >> ;
                               <:expr< Pretty.text ")" >> ;
                               <:expr< Pretty.unalign >> ])
              in
              e
        in
        
        (* Print one constructor *)
        let gen_print_cons (loc, c, tl) =
          let p = gen_print_cons_patt loc c tl in
          let e = gen_print_cons_expr loc c tl in
          p, None, e
        in
        let gen_print_sum loc cdl =
          let pwel = List.map gen_print_cons cdl in
          <:expr< fun [ $list:pwel$ ] >>
        in
        gen_print_sum loc cdl
          
    | TyArr (_, _, _) -> (* An arrow *)
        <:expr< fun _ -> Pretty.text "<func>" >>
          
    | _ -> <:expr< fun _ -> Pretty.text "<type unimplemented>" >>
in


(* For each type declaration of type t1, t2, we generate the following 
 * functions
   let rec d_t1_rec (d_t1: t1 -> doc) (d_t2: t2 -> doc) : t1 -> doc = ...
   and     d_t2_rec (d_t1: t1 -> doc) (d_t2: t2 -> doc) : t2 -> doc = ...

   - in the above functions the arguments are used for the recursive 
     invocations. These functions are used for override. 

   let rec d_t1 = d_t1_rec d_t1 d_t2
   and     d_t2 = d_t2_rec d_t1 d_t2

   - These functions can be used more easily

   let f_t1 () x = d_t1 x
   let f_t2 () x = d_t2 x

   - These functions can be used with format strings
*)
let gen_print_funs (loc: loc) (tdl: type_decl list) : str_item list =

  let gen_one_print_fun (loc: loc) (((locn,n), tpl, (tk: ctyp), 
                                     constraints): type_decl) 
      : patt * expr =
    (* Generate the body of the printing function *)
    let body: expr = 
      if tpl <> [] then 
        <:expr< text "parameterized types not yet implemented" >>
      else if constraints <> [] then 
        <:expr< text "typ constraints not yet implemented" >>
      else
        gen_print_type loc tk
          
    in
    (* Generate the pattern including all the recursive functions *)
    let body': expr = 
      List.fold_right
        (fun ((_, n), _, _, _) acc -> 
          <:expr< fun $lid:p_fun_name n$ -> $acc$ >>)
        tdl
        body
    in
    <:patt< $lid:p_rec_fun_name n$ >>, body'
  in       
  let prec_el: (patt * expr) list = List.map (gen_one_print_fun loc) tdl in
  let rec_printers: str_item = 
    <:str_item< value rec $list:prec_el$ >>
  in
  (* Now generate the actual printers *)
  let p_el: (patt * expr) list = 
    List.map (fun ((loc, n), _, _, _) -> 
      let body = 
        List.fold_left
          (fun acc ((loc, n'), _, _, _) -> 
            <:expr< $acc$ $lid:p_fun_name n'$ >>)
          <:expr< $lid:p_rec_fun_name n$ >>
        tdl
      in
      <:patt< $lid:p_fun_name n$ >>, <:expr< fun x -> $body$ x >>)
      tdl
  in
  let printers: str_item = 
    <:str_item< value rec $list:p_el$ >>
  in
  (* Now generate the format printers *)
  let f_printers: str_item list = 
    List.map 
      (fun ((loc,n), _, _, _) -> 
        <:str_item< value $lid:f_fun_name n$ () = $lid:p_fun_name n$ >>)
      tdl
  in
  rec_printers :: printers :: f_printers
in

 
(* Delete the old rule for parsing types *)
DELETE_RULE
  Pcaml.str_item: "type"; LIST1 Pcaml.type_declaration SEP "and"
END;


DELETE_RULE
  Pcaml.str_item: "let"; OPT "rec"; LIST1 Pcaml.let_binding SEP "and"
END;



DELETE_RULE
  Pcaml.module_expr: "struct"; LIST0 [ Pcaml.str_item; OPT ";;" ] ; "end"
END;


(** Add our type parsing *) 
EXTEND
  Pcaml.str_item:
    [ [ "type"; tdl = LIST1 Pcaml.type_declaration SEP "and" ->
        (* The actual type declarations. Remember them *)
        List.iter (fun ((_, n), _, _, _) -> H.add knownTypes n tdl) tdl;
        if H.mem knownTypes "ALL" then begin 
          (* We must generate the printer for all types *)
          StDcl (loc, StTyp (loc, tdl) ::
                      gen_print_funs loc tdl)
        end else begin 
          StTyp (loc, tdl)
        end

      | "let"; r = OPT "rec"; l = LIST1 Pcaml.let_binding SEP "and" -> 
        (* See if this is ours *)
        let isrec = if r = None then false else true in 
        try 
          match l with 
            [ (PaAny _, e) ] when not isrec -> begin
              match e with 
                <:expr< Pretty.auto_printer $e$ >>
              | <:expr< auto_printer $e$ >> -> begin
                  (* see if we know about such a type *)
                  let n: string = 
                    match e with 
                      ExStr (_, n) -> n
                    | _ -> 
                        Stdpp.raise_with_loc loc 
                          (Failure "auto_printer must have a string literal representing a type name")
                  in
                  if n = "ALL" then begin 
                    H.add knownTypes "ALL";
                    StDcl (loc, [])
                  end else begin
                    try 
                      let tdl = H.find knownTypes n in
                      StDcl (loc, gen_print_funs loc tdl)
                    with Not_found -> 
                      Stdpp.raise_with_loc loc
                        (Failure ("auto_printer invoked for unknown type " ^ n))
                  end
              end
              | _ -> raise Not_found
            end
          | _ -> raise Not_found
        with Not_found -> 
          StVal (loc, isrec, l)
      ]
    ]
  ;

 Pcaml.module_expr: 
   [ [ "struct"; st = LIST0 [ s = Pcaml.str_item; OPT ";" -> s ] ; "end" ->
       (* Found a complete module expr. Now forget the types that are in st *)
       List.iter (fun s -> 
         match s with 
           StTyp (_, td) -> 
             List.iter (fun ((_, n), _, _, _) -> 
               assert (H.mem knownTypes n);
               H.remove knownTypes n)
               td
         | _ -> ())
       st;
       MeStr (loc, st )
   ] ];

END;

(*
let _ = Grammar.Entry.print Pcaml.str_item in
()

*)


