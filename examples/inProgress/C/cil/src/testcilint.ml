open Cilint
open Sys
open List

let op = argv.(1)
let nums = map cilint_of_string (tl (tl (Array.to_list argv)))

let c op = op (nth nums 0)
let cc op = op (nth nums 0) (nth nums 1)
let ci op = op (nth nums 0) (int_of_cilint (nth nums 1))
;;

Printf.printf "op %s" op;
iter (fun n -> Printf.printf " %s" (string_of_cilint n)) nums;

let r = 
  match op with
  | "ts" -> fst (ci truncate_signed_cilint)
  | "tu" -> fst (ci truncate_unsigned_cilint)
  | "--" -> c neg_cilint
  | "+" -> cc add_cilint
  | "-" -> cc sub_cilint
  | "*" -> cc mul_cilint
  | "/" -> cc div0_cilint
  | "%" -> cc rem_cilint
  | "//" -> cc div_cilint
  | "%%" -> cc mod_cilint
  | "~" -> c lognot_cilint
  | "&" -> cc logand_cilint
  | "|" -> cc logor_cilint
  | "^" -> cc logxor_cilint
  | "<<" -> ci shift_left_cilint
  | ">>" -> ci shift_right_cilint
  | "t1" -> cilint_of_int64 (-1L)
  | "t2" -> cilint_of_int64 (0x8000000000000000L)
  | "t3" -> cilint_of_int64 (0x8000000000000001L)
  | "64" -> cilint_of_int64 (int64_of_cilint (nth nums 0))
  | _ -> zero_cilint
in
Printf.printf " gives %s\n" (string_of_cilint r)
