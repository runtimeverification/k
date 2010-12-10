(* camlp5r *)
(* $Id: ioXML.ml,v 1.21 2007/11/14 09:11:59 deraugla Exp $ *)
(* Copyright (c) 2002 INRIA *)

#load "pa_extend.cmo";

type ast =
  [ Tag of (int * int) and string and list ast
  | Str of (int * int) and string ]
;

exception ExcLoc of (int * int) and exn;

value raise_loc loc exc =
  match exc with
  [ ExcLoc _ _ -> raise exc
  | _ -> raise (ExcLoc loc exc) ]
;

value error_txt loc str = raise_loc loc (Stream.Error str);
value error loc str = error_txt loc (str ^ " expected");

(* Buffer machinery *)

value buff = Buffer.create 80;
value store len c =
  do {
    if len = 0 then Buffer.clear buff else ();
    Buffer.add_char buff c;
    Buffer.length buff
  }
;
value get_buff len = if len = 0 then "" else Buffer.contents buff;

(* eval_char and eval_string borrowed to Camlp5 library to avoid having
   to link with it *)

value valch x = Char.code x - Char.code '0';

value rec backslash s i =
  if i = String.length s then raise Not_found
  else
    match s.[i] with
    [ 'n' -> ('\n', i + 1)
    | 'r' -> ('\r', i + 1)
    | 't' -> ('\t', i + 1)
    | 'b' -> ('\b', i + 1)
    | '\\' -> ('\\', i + 1)
    | '0'..'9' as c -> backslash1 (valch c) s (i + 1)
    | _ -> raise Not_found ]
and backslash1 cod s i =
  if i = String.length s then ('\\', i - 1)
  else
    match s.[i] with
    [ '0'..'9' as c -> backslash2 (10 * cod + valch c) s (i + 1)
    | _ -> ('\\', i - 1) ]
and backslash2 cod s i =
  if i = String.length s then ('\\', i - 2)
  else
    match s.[i] with
    [ '0'..'9' as c -> (Char.chr (10 * cod + valch c), i + 1)
    | _ -> ('\\', i - 2) ]
;

value token_eval_char s =
  if String.length s = 1 then s.[0]
  else if String.length s = 0 then failwith "invalid char token"
  else if s.[0] = '\\' then
    if String.length s = 2 && s.[1] = ''' then '''
    else
      try
        let (c, i) = backslash s 1 in
        if i = String.length s then c else raise Not_found
      with
      [ Not_found -> failwith "invalid char token" ]
  else failwith "invalid char token"
;

value special =
  [('<', "&lt;"); ('>', "&gt;"); ('&', "&amp;"); ('"', "&quot;");
   (''', "&apos;")]
;

value xparse_escape s =
  loop 0 0 where rec loop len i =
    if i = String.length s then get_buff len
    else
      let (len, i) =
        match s.[i] with
        [ '&' ->
            loop special where rec loop =
              fun
              [ [(u, t) :: sl] ->
                  let tlen = String.length t in
                  if i + tlen <= String.length s &&
                     String.sub s i tlen = t
                  then
                    (store len u, i + tlen)
                  else loop sl
              | [] -> (store len '&', i + 1) ]
        | c -> (store len c, i + 1) ]
      in
      loop len i
;

(* parsing ast *)

value map f xl = List.rev (List.rev_map f xl);

value xpa_func a _ = failwith "parse_function";

value xpa_tag lab pa_a =
  fun
  [ Tag loc s al when s = lab ->
      match al with
      [ [a] -> pa_a a
      | [] -> error_txt loc "field value missing"
      | [_; Tag loc _ _ | Str loc _ :: _] -> error loc ("</" ^ lab ^ ">") ]
  | Tag loc _ _ | Str loc _ -> error loc lab ]
;

value xpa_ai pa_a =
  fun
  [ Tag _ "ai" [x] -> pa_a x
  | Tag loc _ _ | Str loc _ -> error loc "ai" ]
;

value xpa_ci pa_a =
  fun
  [ Tag _ "ci" [x] -> pa_a x
  | Tag loc _ _ | Str loc _ -> error loc "ci" ]
;

value xpa_li pa_a =
  fun
  [ Tag _ "li" [x] -> pa_a x
  | Tag loc _ _ | Str loc _ -> error loc "li" ]
;

value xpa_ti pa_a =
  fun
  [ Tag _ "ti" [x] -> pa_a x
  | Tag loc _ _ | Str loc _ -> error loc "ti" ]
;

value xpa_tup2 (pa1, pa2) =
  fun
  [ Tag _ "tuple" [x1; x2] -> (xpa_ti pa1 x1, xpa_ti pa2 x2)
  | Tag loc _ _ | Str loc _ -> error loc "tuple with 2 params" ]
;

value xpa_tup3 (pa1, pa2, pa3) =
  fun
  [ Tag _ "tuple" [x1; x2; x3] ->
      (xpa_ti pa1 x1, xpa_ti pa2 x2, xpa_ti pa3 x3)
  | Tag loc _ _ | Str loc _ -> error loc "tuple with 3 params" ]
;

value xpa_tup4 (pa1, pa2, pa3, pa4) =
  fun
  [ Tag _ "tuple" [x1; x2; x3; x4] ->
      (xpa_ti pa1 x1, xpa_ti pa2 x2, xpa_ti pa3 x3, xpa_ti pa4 x4)
  | Tag loc _ _ | Str loc _ -> error loc "tuple with 4 params" ]
;

value xpa_tup5 (pa1, pa2, pa3, pa4, pa5) =
  fun
  [ Tag _ "tuple" [x1; x2; x3; x4; x5] ->
      (xpa_ti pa1 x1, xpa_ti pa2 x2, xpa_ti pa3 x3, xpa_ti pa4 x4,
       xpa_ti pa5 x5)
  | Tag loc _ _ | Str loc _ -> error loc "tuple with 5 params" ]
;

value xparse_array pa_a =
  fun
  [ Tag _ "array" xl -> Array.of_list (map (xpa_ai pa_a) xl)
  | Tag loc _ _ | Str loc _ -> error loc "array" ]
;

value xparse_bool =
  fun
  [ Tag _ "False" [] -> False
  | Tag _ "True" [] -> True
  | Tag loc _ _ | Str loc _ -> error loc "bool" ]
;

value xparse_char =
  fun
  [ Str loc s -> token_eval_char s
  | Tag loc _ _ -> error loc "char" ]
;  

value xparse_int =
  fun
  [ Str loc s -> try int_of_string s with [ Failure _ -> error loc "integer" ]
  | Tag loc _ _ -> error loc "integer" ]
;

value xparse_int64 =
  fun
  [ Str loc s -> try Int64.of_string s with [ Failure _ -> error loc "integer64" ]
  | Tag loc _ _ -> error loc "integer64" ]
;

value xparse_float =
  fun
  [ Str loc s -> try float_of_string s with [ Failure _ -> error loc "float" ]
  | Tag loc _ _ -> error loc "float" ]
;

value xparse_list pa_a =
  fun
  [ Tag _ "list" xl -> List.map (xpa_li pa_a) xl
  | Tag loc _ _ | Str loc _ -> error loc "list" ]
;

value xparse_nativeint =
  fun
  [ Str loc s ->
      try Nativeint.of_string s with [ Failure _ -> error loc "nativeint" ]
  | Tag loc _ _ -> error loc "nativeint" ]
;

value xparse_option pa_a =
  fun
  [ Tag _ "Some" [x1] -> Some (pa_a x1)
  | Tag _ "None" [] -> None
  | Tag loc _ _ | Str loc _ -> error loc "option" ]
;

value rec xparse_ref pa_a =
  fun
  [ Tag _ "ref" [contents] -> {contents = xpa_tag "contents" pa_a contents}
  | Tag loc _ _ | Str loc _ -> error loc "ref" ]
;

value xparse_string =
  fun
  [ Str _ s -> xparse_escape s
  | Tag loc _ _ -> error loc "string" ]
;

(* printing *)

value xprint = Format.fprintf;

value xpr_brec ppf tag =
  xprint ppf "@[<v 2><%s>@," tag
;
value xpr_erec ppf tag =
  xprint ppf "@;<0 -2></%s>@]" tag
;
value xpr_srec ppf =
  xprint ppf "@,"
;
value xpr_rlab lab f ppf e =
  xprint ppf "@[<hv 2><%s>@,%a@;<0 -2></%s>@]" lab f e lab
;
value xpr_bcons ppf c =
  xprint ppf "@[<hv 2><%s>@," c
;
value xpr_econs ppf c =
  xprint ppf "@;<0 -2></%s>@]" c
;
value xpr_scons ppf =
  xprint ppf "@,"
;
value xpr_acons ppf c =
  xprint ppf "<%s/>" c
;
value xpr_func ppf _ = failwith "print_function";

value xpr_ai pr ppf x =
  xprint ppf "%a%a%a" xpr_bcons "ai" pr x xpr_econs "ai"
;

value xpr_ci pr ppf x =
  xprint ppf "%a%a%a" xpr_bcons "ci" pr x xpr_econs "ci"
;

value xpr_li pr ppf x =
  xprint ppf "%a%a%a" xpr_bcons "li" pr x xpr_econs "li"
;

value xpr_ti pr ppf x =
  xprint ppf "%a%a%a" xpr_bcons "ti" pr x xpr_econs "ti"
;

value xpr_tup2 (pr1, pr2) ppf (x1, x2) =
  xprint ppf "%a%a%t%a%a"
    xpr_bcons "tuple" (xpr_ti pr1) x1 xpr_scons (xpr_ti pr2) x2
    xpr_econs "tuple"
;

value xpr_tup3 (pr1, pr2, pr3) ppf (x1, x2, x3) =
  xprint ppf "%a%a%t%a%t%a%a"
    xpr_bcons "tuple" (xpr_ti pr1) x1 xpr_scons (xpr_ti pr2) x2
    xpr_scons (xpr_ti pr3) x3 xpr_econs "tuple"
;

value xpr_tup4 (pr1, pr2, pr3, pr4) ppf (x1, x2, x3, x4) =
  xprint ppf "%a%a%t%a%t%a%t%a%a"
    xpr_bcons "tuple" (xpr_ti pr1) x1 xpr_scons (xpr_ti pr2) x2
    xpr_scons (xpr_ti pr3) x3 xpr_scons (xpr_ti pr4) x4
    xpr_econs "tuple"
;

value xpr_tup5 (pr1, pr2, pr3, pr4, pr5) ppf (x1, x2, x3, x4, x5) =
  xprint ppf "%a%a%t%a%t%a%t%a%t%a%a"
    xpr_bcons "tuple" (xpr_ti pr1) x1 xpr_scons (xpr_ti pr2) x2
    xpr_scons (xpr_ti pr3) x3 xpr_scons (xpr_ti pr4) x4 xpr_scons
    (xpr_ti pr5) x5 xpr_econs "tuple"
;

value xprint_array pr_a ppf array =
  do {
    xpr_bcons ppf "array";
    if Array.length array = 0 then ()
    else do {
      xprint ppf "%a" (xpr_ai pr_a) array.(0);
      for i = 1 to Array.length array - 1 do {
        xprint ppf "@ %a" (xpr_ai pr_a) array.(i);
      }
    };
    xpr_econs ppf "array";
  }
;

value xprint_list pr_a ppf list =
  do {
    xpr_bcons ppf "list";
    match list with
    [ [] -> ()
    | [e :: el] ->
        do {
          xprint ppf "%a" (xpr_li pr_a) e;
          List.iter (fun e -> xprint ppf "@ %a" (xpr_li pr_a) e) el
        } ];
    xpr_econs ppf "list";
  }
;

value xprint_bool ppf b = xpr_acons ppf (if b then "True" else "False");
value xprint_char ppf c = xprint ppf "\"%s\"" (Char.escaped c);
value xprint_int ppf i = xprint ppf "%d" i;
value xprint_int64 ppf i = xprint ppf "%s" (Int64.to_string i);
value xprint_float ppf f = xprint ppf "\"%s\"" (string_of_float f);
value xprint_nativeint ppf n = xprint ppf "\"%s\"" (Nativeint.to_string n);

value xprint_option pr_a ppf =
  fun
  [ Some x1 -> xprint ppf "%a%a%a" xpr_bcons "Some" pr_a x1 xpr_econs "Some"
  | None -> xpr_acons ppf "None" ]
;

value rec xprint_ref pr_a ppf x =
  xprint ppf "%a%a%a%a%a" xpr_bcons "ref" xpr_bcons "contents" pr_a x.contents
    xpr_econs "contents" xpr_econs "ref"
;

value xprint_escape ppf s =
  for i = 0 to String.length s -1 do {
    match s.[i] with
    [ '<' -> xprint ppf "&lt;"
    | '>' -> xprint ppf "&gt;"
    | '&' -> xprint ppf "&amp;"
    | '"' -> xprint ppf "&quot;"
    | ''' -> xprint ppf "&apos;"
    | c -> xprint ppf "%c" c ]
  }
;

value xprint_string ppf s = xprint ppf "\"%a\"" xprint_escape s;

(* parsing from stream to ast *)

type loc = (int * int);

type token =
  [ Tequal of loc
  | Teoi of loc
  | Tgreater of loc
  | Tident of loc and string
  | Tint of loc and string
  | Tless of loc
  | Tlessslash of loc
  | Tslash of loc
  | Tstring of loc and string ]
;

value rec ident len =
  parser
  [ [: `(('a'..'z' | 'A'..'Z' | '_' | '0'..'9' | ''') as c); s :] ->
      ident (store len c) s
  | [: :] -> get_buff len ]
;

value rec number len =
  parser
  [ [: `('0'..'9' as c); s :] -> number (store len c) s
  | [: :] -> get_buff len ]
;

value rec string len =
  parser
  [ [: `'"' :] -> get_buff len
  | [: `'\\'; `c; s :] -> string (store (store len '\\') c) s
  | [: `c; s :] -> string (store len c) s ]
;

value less bp =
  parser
  [ [: `'/' :] ep -> Tlessslash (bp, ep)
  | [: :] ep -> Tless (bp, ep) ]
;

value rec lexer_func =
  parser bp
  [ [: `' ' | '\t' | '\r' | '\n'; s :] -> lexer_func s
  | [: `'<'; t = less bp :] -> t
  | [: `'"'; s = string 0 :] ep -> Tstring (bp, ep) s
  | [: `('0'..'9' | '-' as c); s = number (store 0 c) :] ep -> Tint (bp, ep) s
  | [: `('a'..'z' | 'A'..'Z' as c); s = ident (store 0 c) :] ep ->
      Tident (bp, ep) s
  | [: `'=' :] ep -> Tequal (bp, ep)
  | [: `'/' :] ep -> Tslash (bp, ep)
  | [: `'>' :] ep -> Tgreater (bp, ep)
  | [: :] ep -> Teoi (bp, ep) ]
;

value rec xml_list rev_list =
  parser
  [ [: x = xml; s :] -> xml_list [x :: rev_list] s
  | [: :] -> List.rev rev_list ]
and xml =
  parser
  [ [: `Tless (bp, _); `Tident _ bt  ? "identifier expected";
       _ = attr_list [];
       t =
         parser
         [ [: `Tslash _; `Tgreater (_, ep) ? "'>' expected" :] ->
             Tag (bp, ep) bt []
         | [: `Tgreater (_, ep); el = xml_list [];
               (et, loc1) = end_tag ? "end tag expected" :] ->
             if et <> bt then
               raise_loc loc1
                 (Stream.Error ("</" ^ bt ^ "> expected"))
             else Tag (bp, ep) bt el ] :] -> t
  | [: (s, loc) = string :] -> Str loc s ]
and end_tag =
  parser
  [ [: `Tlessslash (bp, _); `Tident _ i ? "identifier expected";
       `Tgreater (_, ep) ? "'>' expected" :] ->
      (i, (bp, ep)) ]
and attr_list rev_list =
  parser
  [ [: x = attribute; s :] -> attr_list [x :: rev_list] s
  | [: :] -> List.rev rev_list ]
and attribute =
  parser
  [ [: `Tident _ k; `Tequal _ ? "'=' expected";
       (v, _) = string ? "string or integer expected" :] -> (k, v) ]
and string =
  parser
  [ [: `Tstring loc s :] -> (s, loc)
  | [: `Tint loc s :] -> (s, loc) ]
;

value get_loc cstrm strm =
  match Stream.peek strm with
  [ Some x ->
      match x with
      [ Tequal loc
      | Teoi loc
      | Tgreater loc
      | Tident loc _
      | Tint loc _
      | Tless loc
      | Tlessslash loc
      | Tslash loc
      | Tstring loc _ -> loc ]
  | _ -> let bp = Stream.count strm in (bp, bp + 1) ]
;

value parse_xml cstrm =
  let strm = Stream.from (fun _ -> Some (lexer_func cstrm)) in
  try xml strm with e -> raise_loc (get_loc cstrm strm) e
;

value parse_xml_list cstrm =
  let strm = Stream.from (fun _ -> Some (lexer_func cstrm)) in
  let r =
    try xml_list [] strm with e ->
      raise_loc (get_loc cstrm strm) e
  in
  match strm with parser
  [ [: `Teoi _ :] -> r
  | [: :] ->
      raise_loc (get_loc cstrm strm)
        (Stream.Error ("End of input expected")) ]
;
