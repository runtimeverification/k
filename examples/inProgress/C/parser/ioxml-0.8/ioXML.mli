(* camlp5r *)
(* $Id: ioXML.mli,v 1.17 2007/11/14 09:11:59 deraugla Exp $ *)
(* Copyright (c) 2002 INRIA *)

open Format;

(** Ast type for XML input *)
type ast =
  [ Tag of (int * int) and string and list ast
  | Str of (int * int) and string ]
;

exception ExcLoc of (int * int) and exn;
(** exception with the source location *)

value parse_xml_list : Stream.t char -> list ast;
(** parse a stream up to the end *)

value parse_xml : Stream.t char -> ast;
(** parse just one xml item *)

(* The default parsers en printers for predefined types.
   Can be hidden if you redefine them in your input file. *)

value xparse_array : (ast -> 'a) -> ast -> array 'a;
value xparse_bool : ast -> bool;
value xparse_char : ast -> char;
value xparse_int : ast -> int;
value xparse_float : ast -> float;
value xparse_list : (ast -> 'a) -> ast -> list 'a;
value xparse_nativeint : ast -> nativeint;
value xparse_option : (ast -> 'a) -> ast -> option 'a;
value xparse_ref : (ast -> 'a) -> ast -> ref 'a;
value xparse_string : ast -> string;

value xprint_array :
  (formatter -> 'a -> unit) -> formatter -> array 'a -> unit;
value xprint_bool : formatter -> bool -> unit;
value xprint_char : formatter -> char -> unit;
value xprint_int : formatter -> int -> unit;
value xprint_float : formatter -> float -> unit;
value xprint_list :
  (formatter -> 'a -> unit) -> formatter -> list 'a -> unit;
value xprint_nativeint : formatter -> nativeint -> unit;
value xprint_option :
  (formatter -> 'a -> unit) -> formatter -> option 'a -> unit;
value xprint_ref :
  (formatter -> 'a -> unit) -> formatter -> ref 'a -> unit;
value xprint_string : formatter -> string -> unit;

(**/**)

value error : (int * int) -> string -> 'a;

value xprint : formatter -> format 'a formatter unit -> 'a;

value xpa_func : ast -> ('a -> 'b);
value xpa_tag : string -> (ast -> 'a) -> ast -> 'a;
value xpa_tup2 : (ast -> 'a * ast -> 'b) -> ast -> ('a * 'b);
value xpa_tup3 : (ast -> 'a * ast -> 'b * ast -> 'c) -> ast -> ('a * 'b * 'c);
value xpa_tup4 :
  (ast -> 'a * ast -> 'b * ast -> 'c * ast -> 'd) -> ast ->
    ('a * 'b * 'c * 'd);
value xpa_tup5 :
  (ast -> 'a * ast -> 'b * ast -> 'c * ast -> 'd * ast -> 'e) -> ast ->
     ('a * 'b * 'c * 'd * 'e);
value xpa_ti : (ast -> 'a) -> ast -> 'a;
value xpa_ci : (ast -> 'a) -> ast -> 'a;

value xpr_func : formatter -> ('a -> 'b) -> unit;
value xpr_tup2 :
  (formatter -> 'a -> unit * formatter -> 'b -> unit) -> formatter ->
     ('a * 'b) -> unit;
value xpr_tup3 :
  (formatter -> 'a -> unit * formatter -> 'b -> unit *
   formatter -> 'c -> unit) -> formatter ->
     ('a * 'b * 'c) -> unit;
value xpr_tup4 :
  (formatter -> 'a -> unit * formatter -> 'b -> unit *
   formatter -> 'c -> unit * formatter -> 'd -> unit) -> formatter ->
     ('a * 'b * 'c * 'd) -> unit;
value xpr_tup5 :
  (formatter -> 'a -> unit * formatter -> 'b -> unit *
   formatter -> 'c -> unit * formatter -> 'd -> unit *
   formatter -> 'e -> unit) -> formatter ->
     ('a * 'b * 'c * 'd * 'e) -> unit;
value xpr_ti : (formatter -> 'a -> unit) -> formatter -> 'a -> unit;
value xpr_ci : (formatter -> 'a -> unit) -> formatter -> 'a -> unit;

value xpr_brec : formatter -> string -> unit;
value xpr_erec : formatter -> string -> unit;
value xpr_srec : formatter -> unit;
value xpr_rlab :
  string -> (formatter -> 'a -> unit) -> formatter -> 'a -> unit;

value xpr_bcons : formatter -> string -> unit;
value xpr_econs : formatter -> string -> unit;
value xpr_scons : formatter -> unit;
value xpr_acons : formatter -> string -> unit;
