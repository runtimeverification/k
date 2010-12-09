(* camlp5r *)
(* $Id: pa_ioXML.ml,v 1.26 2007/11/14 09:11:59 deraugla Exp $ *)
(* Copyright (c) 2002 INRIA *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

value version = "0.8";

value unit = ref False;
Pcaml.add_option "-unit" (Arg.Set unit)
  "        Add \"unit\" type constraints in iter functions.";

value notyp = ref False;
Pcaml.add_option "-notyp" (Arg.Set notyp)
  "       Don't generate types definitions.";

value onepr = ref False;
Pcaml.add_option "-onepr" (Arg.Set onepr)
  "       For each printer, generate one xprint instead of a sequence";

value print_version () =
  do {
    Printf.eprintf "IoXML version %s\n" version;
    flush stderr;
    exit 1
  }
;

Pcaml.add_option "-ioxml_v" (Arg.Unit print_version)
  "     Print IoXML version number and exit.";

value pname cnt = "x" ^ string_of_int cnt;
value fun_name meta_name type_name = meta_name ^ "_" ^ type_name;

value error loc s = <:expr< IoXML.error loc $str:s$ >>;

exception NotImpl of MLast.loc;

value gen_xprint_format loc c xpri el =
  let str =
    loop el where rec loop =
      fun
      [ [] -> ""
      | [_] -> "%a"
      | [_ :: el] -> "%a%t" ^ loop el ]
  in
  let body = <:expr< IoXML.xprint ppf $str:"%a" ^ str ^ "%a"$ >> in
  let body = <:expr< $body$ xpr_bcons $str:c$ >> in
  let (body, _) =
    List.fold_left
      (fun (body, cnt) e ->
         let body = if cnt = 1 then body else <:expr< $body$ xpr_scons >> in
         let e = if xpri <> "" then <:expr< $lid:xpri$ $e$ >> else e in
         let body = <:expr< $body$ $e$ $lid:"x" ^ string_of_int cnt$ >> in
         (body, cnt + 1))
      (body, 1) el
  in
  <:expr< $body$ xpr_econs $str:c$ >>
;

value gen_pa_tup loc tname el =
  let len = List.length el in
  let (pl, el, _) =
    List.fold_right
      (fun e (pl, el, cnt) ->
         let n = "x" ^ string_of_int cnt in
         let p = <:patt< $lid:n$ >> in
         let e = <:expr< (xpa_ti $e$) $lid:n$ >> in
         (<:patt< [$p$ :: $pl$] >>, [e :: el], cnt - 1))
      el (<:patt< [] >>, [], len)
  in
  <:expr<
    fun
    [ IoXML.Tag _ "tuple" $pl$ -> ($list:el$)
    | IoXML.Tag loc _ _ | Str loc _ ->
        IoXML.error loc $str:"tuple with " ^ string_of_int len ^ " params"$ ]
  >>
;

value gen_pr_tup loc tname el =
  let (pl, _) =
    List.fold_left
      (fun (pl, cnt) _ ->
         ([<:patt< $lid:"x" ^ string_of_int cnt$ >> :: pl], cnt + 1))
      ([], 1) el
  in
  let body = gen_xprint_format loc "tuple" "xpr_ti" el in
  <:expr< fun ppf ($list:List.rev pl$) -> $body$ >>
;

value expr_of_type is_parser name sname =
  eot where rec eot t =
    let loc = MLast.loc_of_ctyp t in
    match t with
    [ <:ctyp< '$s$ >> -> <:expr< $lid:sname ^ "_" ^ s$ >>
    | <:ctyp< $lid:s$ >> -> <:expr< $lid:fun_name name s$ >>
    | <:ctyp< $uid:m$ >> -> <:expr< $uid:m$ >>
    | <:ctyp< $t1$ $t2$ >> -> <:expr< $eot t1$ $eot t2$ >>
    | <:ctyp< $t1$.$t2$ >> -> <:expr< $eot t1$.$eot t2$ >>
    | <:ctyp< $_$ -> $_$ >> -> <:expr< $lid:"x" ^ sname ^ "_func"$ >>
    | <:ctyp< ($list:tl$) >> ->
        let el = List.map eot tl in
        let tname = "x" ^ sname ^ "_tup" ^ string_of_int (List.length tl) in
        if List.length el <= 5 then <:expr< $lid:tname$ ($list:el$) >>
        else if is_parser then gen_pa_tup loc tname el
        else gen_pr_tup loc tname el
    | _ -> raise (NotImpl loc) ]
;

value xparse_of_type = expr_of_type True "xparse" "pa";
value xprint_of_type = expr_of_type False "xprint" "pr";

(* xprint type *)

value begin_record loc lab = <:expr< xpr_brec ppf $str:lab$ >>;
value end_record loc lab = <:expr< xpr_erec ppf $str:lab$ >>;
value field_sep loc = <:expr< xpr_srec ppf >>;
value record_lab loc lab f e = <:expr< xpr_rlab $str:lab$ $f$ ppf $e$ >>;

value begin_cons loc c = <:expr< xpr_bcons ppf $str:c$ >>;
value end_cons loc c = <:expr< xpr_econs ppf $str:c$ >>;
value alone_cons loc c = <:expr< xpr_acons ppf $str:c$ >>;
value cons_psep loc = <:expr< xpr_scons ppf >>;

value gen_xprint_cons loc c tl =
  if onepr.val then
    let el = List.map xprint_of_type tl in
    match el with
    [ [] -> alone_cons loc c
    | [_] -> gen_xprint_format loc c "" el
    | _ -> gen_xprint_format loc c "xpr_ci" el ]
  else
    let el = List.map xprint_of_type tl in
    let (rev_el, _) =
      List.fold_left
        (fun (el, cnt) f ->
           let el =
             let f = if List.length tl = 1 then f else <:expr< xpr_ci $f$ >> in
             let e = <:expr< $f$ ppf $lid:pname cnt$ >> in
             let e = if unit.val then <:expr< ($e$ : unit) >> else e in
             [cons_psep loc; e :: el]
           in
           (el, cnt + 1))
        ([], 1) el
    in
    match rev_el with
    [ [] -> alone_cons loc c
    | [_ :: rev_el] ->
          let el =
            [begin_cons loc c :: List.rev [end_cons loc c :: rev_el]]
          in
          <:expr< do { $list:el$ } >> ]
;

value unvala x = IFDEF CAMLP5 THEN Pcaml.unvala x ELSE x END;

value gen_output_cons (loc, c, tl) =
  let c = unvala c in
  let tl = unvala tl in
  let p =
    let p = <:patt< $uid:c$ >> in
    let (p, _) =
      List.fold_left
        (fun (p, cnt) _ ->
           let p = <:patt< $p$ $lid:pname cnt$ >> in
           (p, cnt + 1))
        (p, 1) tl
    in
    p
  in
  let e = gen_xprint_cons loc c tl in
  (p, <:vala< None >>, e)
;

value gen_output_record loc n lbl =
  let n = unvala n in
  if onepr.val then
    let str =
      loop lbl where rec loop =
        fun
        [ [] -> ""
        | [_] -> "%a"
        | [_ :: lbl] -> "%a%t" ^ loop lbl ]
    in
    let str = "%a" ^ str ^ "%a" in
    let body = <:expr< IoXML.xprint ppf $str:str$ >> in
    let body = <:expr< $body$ xpr_brec $str:n$ >> in
    let (body, _) =
      List.fold_left
        (fun (body, first) (loc, lab, mut, t) ->
           let f = xprint_of_type t in
           let e = <:expr< x.$lid:lab$ >> in
           let body = if first then body else <:expr< $body$ xpr_srec >> in
           let body = <:expr< $body$ (xpr_rlab $str:lab$ $f$) $e$ >> in
           (body, False))
        (body, True) lbl
    in
    <:expr< $body$ xpr_erec $str:n$ >>
  else
    let el =
      List.fold_left
        (fun el (loc, lab, mut, t) ->
           let f = xprint_of_type t in
           let e = <:expr< x.$lid:lab$ >> in
           let cut = field_sep loc in
           let e = record_lab loc lab f e in
           [cut; e :: el])
        [] lbl
    in
    let el =
      match el with
      [ [] -> []
      | [_ :: el] -> el ]
    in
    let el = [begin_record loc n :: List.rev [end_record loc n :: el]] in
    <:expr< do { $list:el$ } >>
;

value gen_output_sum loc cdl =
  <:expr< fun ppf -> fun [ $list:List.map gen_output_cons cdl$ ] >>
;

value gen_output_record loc n lbl =
  <:expr< fun ppf x -> $gen_output_record loc n lbl$ >>
;

value gen_output_abstract loc n =
  let n = unvala n in
  let txt = fun_name "xprint" n ^ ": abstract type" in
  <:expr< fun ppf -> failwith $str:txt$ >>
;

value gen_output_funs loc tdl sil =
  let pel =
    List.fold_right
      (fun td pel ->
         let ((loc, n), tpl, tk, cl) =
           IFDEF CAMLP5 THEN
             (td.MLast.tdNam, td.MLast.tdPrm, td.MLast.tdDef, td.MLast.tdCon)
           ELSE td END
         in
         let body =
           loop tk where rec loop =
             fun
             [ <:ctyp< [ $list:cdl$ ] >> -> gen_output_sum loc cdl
             | <:ctyp< { $list:lel$ } >> -> gen_output_record loc n lel
             | <:ctyp< '$_$ >> -> gen_output_abstract loc n
             | <:ctyp< $_$ == $t$ >> -> loop t
             | tk ->
                 let body = xprint_of_type tk in
                 match body with
                 [ <:expr< fun [ $list:_$ ] >> -> body
                 | _ -> <:expr< fun ppf -> $body$ ppf >> ] ]
         in
         let body =
           List.fold_right
             (fun (v, _) e ->
                let v = unvala v in
                <:expr< fun $lid:"pr_" ^ v$ -> $e$ >>)
             (unvala tpl) body
         in
         let n = unvala n in
         [(<:patt< $lid:fun_name "xprint" n$ >>, body) :: pel])
    tdl []
  in
  if pel <> [] then [<:str_item< value rec $list:pel$ >> :: sil] else sil
;

(* xparse type *)

value gen_input_cons (loc, c, tl) =
  let c = unvala c in
  let tl = unvala tl in
  let p =
    let p = <:patt< IoXML.Tag _ $str:c$ >> in
    let (pl, _) =
      List.fold_right
        (fun _ (p, cnt) ->
           let p = <:patt< [$lid:pname cnt$ :: $p$] >> in
           (p, cnt - 1))
        tl (<:patt< [] >>, List.length tl)
    in
    <:patt< $p$ $pl$ >>
  in
  let (e, _) =
    List.fold_left
      (fun (f, cnt) t ->
         let n = <:expr< $lid:pname cnt$ >> in
         let e = xparse_of_type t in
         let e = if List.length tl = 1 then e else <:expr< xpa_ci $e$ >> in
         let e =
            match e with
            [ <:expr< fun [ $list:pel$ ] >> ->
                 <:expr< match $n$ with [ $list:pel$ ] >>
            | e -> <:expr< $e$ $n$ >> ]
         in
         (<:expr< $f$ $e$ >>, cnt + 1))
      (<:expr< $uid:c$ >>, 1) tl
  in
  (p, <:vala< None >>, e)
;

value gen_input_labels loc lbl =
  let pel =
    List.map
      (fun (loc, lab, mut, t) ->
         let p = <:patt< $lid:lab$ >> in
         let e =
           let f = xparse_of_type t in
           <:expr< IoXML.xpa_tag $str:lab$ $f$ $lid:lab$ >>
         in
         (p, e))
      lbl
  in
  <:expr< { $list:pel$ } >>
;

value gen_input_sum loc n cdl =
  let pel =
    List.map gen_input_cons cdl @
    [(<:patt< IoXML.Tag loc _ _ | IoXML.Str loc _ >>, <:vala< None >>,
      error loc n)] 
  in
  <:expr< fun [ $list:pel$ ] >>
;

value gen_input_record loc n lbl =
  let al =
    List.fold_right
      (fun (loc, lab, mut, t) p -> <:patt< [$lid:lab$ :: $p$] >>)
      lbl <:patt< [] >>
  in
  <:expr<
     fun
     [ IoXML.Tag _ $str:n$ $al$ -> $gen_input_labels loc lbl$
     | IoXML.Tag loc _ _ | IoXML.Str loc _ -> $error loc n$ ]
  >>
;

value gen_input_abstract loc n =
  let txt = fun_name "xparse" n ^ ": abstract type" in
  <:expr< fun ast -> failwith $str:txt$ >>
;

value gen_input_funs loc tdl sil =
  let pel =
    List.fold_right
      (fun td pel ->
         let ((loc, n), tpl, tk, cl) =
           IFDEF CAMLP5 THEN
             (td.MLast.tdNam, td.MLast.tdPrm, td.MLast.tdDef, td.MLast.tdCon)
           ELSE td END
         in
         let n = unvala n in
         let body =
           loop tk where rec loop =
             fun
             [ <:ctyp< [ $list:cdl$ ] >> -> gen_input_sum loc n cdl
             | <:ctyp< { $list:lel$ } >> -> gen_input_record loc n lel
             | <:ctyp< '$_$ >> -> gen_input_abstract loc n
             | <:ctyp< $_$ == $t$ >> -> loop t
             | tk ->
                 let body = xparse_of_type tk in
                 match body with
                 [ <:expr< fun [ $list:_$ ] >> -> body
                 | _ ->  <:expr< fun ast -> $body$ ast >> ] ]
         in
         let body =
           List.fold_right
             (fun (v, _) e ->
                let v = unvala v in
                <:expr< fun $lid:"pa_" ^ v$ -> $e$ >>)
             (unvala tpl) body
         in
         [(<:patt< $lid:fun_name "xparse" n$ >>, body) :: pel])
    tdl []
  in
  if pel <> [] then [<:str_item< value rec $list:pel$ >> :: sil] else sil
;

(* *)

value gen_ioxml_impl loc tdl =
  try
    let sil = [] in
    let sil = gen_output_funs loc tdl sil in
    let sil = gen_input_funs loc tdl sil in
    sil
  with
  [ NotImpl loc ->
      do {
        Pcaml.warning.val loc "Warning: IoXML not implemented for this type";
        []
      } ]
;

(* Interface *)

value make_type_with_params loc n tpl =
  List.fold_left (fun t (tp, _) -> <:ctyp< $t$ '$unvala tp$ >>)
    <:ctyp< $lid:n$ >> tpl
;

value gen_output_funs_intf loc tdl sil =
  let itl =
    List.fold_right
      (fun td itl ->
         let ((loc, n), tpl, tk, cl) =
           IFDEF CAMLP5 THEN
             (td.MLast.tdNam, td.MLast.tdPrm, td.MLast.tdDef, td.MLast.tdCon)
           ELSE td END
         in
         let n = unvala n in
         let tpl = unvala tpl in
         let t = make_type_with_params loc n tpl in
         let t = <:ctyp< Format.formatter -> $t$ -> unit >> in
         let t =
           List.fold_right
             (fun (tp, _) t ->
                let tp = unvala tp in
                <:ctyp< (Format.formatter -> '$tp$ -> unit) -> $t$ >>)
             tpl t
         in
         [(fun_name "xprint" n, t) :: itl])
    tdl []
  in
  if itl <> [] then
    List.map (fun (i, t) -> <:sig_item< value $i$ : $t$ >>) itl @ sil
  else sil
;

value gen_input_funs_intf loc tdl sil =
  let itl =
    List.fold_right
      (fun td itl ->
         let ((loc, n), tpl, tk, cl) =
           IFDEF CAMLP5 THEN
             (td.MLast.tdNam, td.MLast.tdPrm, td.MLast.tdDef, td.MLast.tdCon)
           ELSE td END
         in
         let n = unvala n in
         let tpl = unvala tpl in
         let t = make_type_with_params loc n tpl in
         let t = <:ctyp< IoXML.ast -> $t$ >> in
         let t =
           List.fold_right
             (fun (tp, _) t ->
                let tp = unvala tp in
                <:ctyp< (IoXML.ast -> '$tp$) -> $t$ >>)
             tpl t
         in
         [(fun_name "xparse" n, t) :: itl])
    tdl []
  in
  if itl <> [] then
    List.map (fun (i, t) -> <:sig_item< value $i$ : $t$ >>) itl @ sil
  else sil
;

value gen_ioxml_intf loc tdl =
  try
    let sil = [] in
    let sil = gen_output_funs_intf loc tdl sil in
    let sil = gen_input_funs_intf loc tdl sil in
    sil
  with
  [ NotImpl loc ->
      do {
        Pcaml.warning.val loc "Warning: IoXML not implemented for this type";
        []
      } ]
;

EXTEND
  Pcaml.str_item:
    [ [ "type"; LIDENT "nogen";
        tdl = LIST1 Pcaml.type_declaration SEP "and" ->
          <:str_item< type $list:tdl$ >>
      | "type"; tdl = LIST1 Pcaml.type_declaration SEP "and" ->
          let sil = gen_ioxml_impl loc tdl in
          let sil =
            if notyp.val then sil
            else [<:str_item< type $list:tdl$ >> :: sil]
          in
          <:str_item< declare $list:sil$ end >> ] ]
  ;
  Pcaml.sig_item:
    [ [ "type"; LIDENT "nogen";
        tdl = LIST1 Pcaml.type_declaration SEP "and" ->
          <:sig_item< type $list:tdl$ >>
      | "type"; tdl = LIST1 Pcaml.type_declaration SEP "and" ->
          let sil = gen_ioxml_intf loc tdl in
          let sil = [<:sig_item< type $list:tdl$ >> :: sil] in
          <:sig_item< declare $list:sil$ end >> ] ]
  ;
END;

value first = ref True;

Pcaml.parse_implem.val :=
  fun strm ->
    let (sil, stopped) = Grammar.Entry.parse Pcaml.implem strm in
    let sil =
      if first.val then
        let _ = do { first.val := False } in
        let loc = Stdpp.dummy_loc in
        [(<:str_item< open IoXML >>, loc) :: sil]
      else sil
    in
    (sil, stopped)
;

Pcaml.parse_interf.val :=
  fun strm ->
    let (sil, stopped) = Grammar.Entry.parse Pcaml.interf strm in
    let sil =
      if first.val then
        let _ = do { first.val := False } in
        let loc = Stdpp.dummy_loc in
        [(<:sig_item< open IoXML >>, loc) :: sil]
      else sil
    in
    (sil, stopped)
;

IFDEF OCAML_305 THEN
  Pcaml.inter_phrases.val := Some "\n\n"
END;
