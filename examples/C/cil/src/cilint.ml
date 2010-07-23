(* cilint: infinite-precision, 2's complement arithmetic. *)

(* An infinite-precision 2's complement number is a good way of
   understanding the meaning of bitwise operations on infinite
   precision numbers: positive numbers have the normal base-2
   representation, while negative numbers are represented in
   a 2's complement representation with an infinite series of
   leading 1 bits. I.e.,

     3 = ...0000000000011
    -3 = ...1111111111101

   We represent cilints using a big_int, except that we specialise the
   case where the number fits in a regular int. This specialisation
   has two benefits:
   - more compact (and potentially faster ops, though more would need to be
   specialised for this to be really worth it)
   - ability to see the value of small constants in ocamldebug

   The implementation can be simplified once OCaml 3.11.1 shows up, with
   bitwise operations on big_ints, and bug-fixed versions of int64_of_big_int
   and big_int_of_int64. *)

open Big_int
  
type cilint = Small of int | Big of big_int
type truncation = NoTruncation | ValueTruncation | BitTruncation

let zero_cilint = Small 0
let one_cilint = Small 1

(* Precompute useful big_ints *)
let b30 = power_int_positive_int 2 30
let m1 = minus_big_int unit_big_int

(* True if 'b' is all 0's or all 1's *)
let nobits (b:big_int) : bool = 
  sign_big_int b = 0 || compare_big_int b m1 = 0

let big_int_of_cilint (c:cilint) : big_int = 
  match c with
  | Small i -> big_int_of_int i
  | Big b -> b

let cilint_of_big_int (b:big_int) : cilint = 
  if is_int_big_int b then
    Small (int_of_big_int b)
  else
    Big b

let neg_cilint c = 
  match c with
  | Small i when i <> min_int -> Small (-i)
  | _ -> Big (minus_big_int (big_int_of_cilint c))

(* Apply big_int 'op' to two cilints, returning a cilint *)
let b op c1 c2 = cilint_of_big_int (op (big_int_of_cilint c1) (big_int_of_cilint c2))
  
let add_cilint = b add_big_int
let sub_cilint = b sub_big_int
let mul_cilint = b mult_big_int
let div_cilint = b div_big_int
let mod_cilint = b mod_big_int

let compare_cilint (c1:cilint) (c2:cilint) : int = 
  match c1, c2 with
  | Small i1, Small i2 -> compare i1 i2
  | _ -> compare_big_int (big_int_of_cilint c1) (big_int_of_cilint c2)

let is_zero_cilint (c:cilint) : bool = 
  match c with
  | Small i -> i = 0
  | Big b -> sign_big_int b = 0

let negative_cilint (c:cilint) : bool = 
  match c with 
  | Small i -> i < 0
  | Big b -> sign_big_int b < 0

let cilint_of_int (i:int) : cilint = Small i

let int_of_cilint (c:cilint) : int = 
  match c with 
  | Small i -> i
  | Big b -> int_of_big_int b

let rec cilint_of_int64 (i64:int64) : cilint = 
  if Int64.compare i64 (Int64.of_int min_int) >= 0 && 
    Int64.compare i64 (Int64.of_int max_int) <= 0 then
    Small (Int64.to_int i64)
  else
    (* We convert 30 bits at a time *)
    let rec loop i mul acc = 
      if i = 0L then acc
      else if i = -1L then sub_big_int acc mul
      else 
	let lo30 = Int64.to_int (Int64.logand i 0x3fffffffL) in
	loop (Int64.shift_right i 30) (mult_big_int mul b30)
	  (add_big_int acc (mult_big_int mul (big_int_of_int lo30)))
    in Big (loop i64 unit_big_int zero_big_int)
   
(* Note that this never fails, instead it returns the low-order 64-bits
   of the cilint. *)
let rec int64_of_cilint (c:cilint) : int64 = 
  match c with
  | Small i -> Int64.of_int i
  | Big b -> 
      let rec loop b mul acc = 
	if sign_big_int b = 0 then 
	  acc
	else if compare_big_int b m1 == 0 then
	  Int64.sub acc mul
	else
	  let hi, lo = quomod_big_int b b30 in
	  loop hi (Int64.mul mul 0x40000000L)
	    (Int64.add acc (Int64.mul mul (Int64.of_int (int_of_big_int lo))))
      in loop b 1L 0L
      
let cilint_of_string (s:string) : cilint = 
  cilint_of_big_int (big_int_of_string s)

let string_of_cilint (c:cilint) : string = 
  match c with 
  | Small i -> string_of_int i
  | Big b -> string_of_big_int b

(* Divide rounding towards zero *)
let div0_cilint (c1:cilint) (c2:cilint) = 
  match c1, c2 with
  | Small i1, Small i2 -> Small (i1 / i2)
  | _ ->
      let b1 = big_int_of_cilint c1 in
      let b2 = big_int_of_cilint c2 in 
      let q, r = quomod_big_int b1 b2 in
      if lt_big_int b1 zero_big_int && (not (eq_big_int r zero_big_int)) then
	if gt_big_int b2 zero_big_int then
	  Big (succ_big_int q)
	else
	  Big (pred_big_int q)
      else
	Big q

(* And the corresponding remainder *)
let rem_cilint (c1:cilint) (c2:cilint) = 
  (sub_cilint c1 (mul_cilint c2 (div0_cilint c1 c2)))

(* Perform logical op 'op' over 'int' on two cilints. Does it work
   30-bits at a time as that is guaranteed to fit in an 'int'. *)
let logop op c1 c2 = 
  match c1, c2 with
  | Small i1, Small i2 -> Small (op i1 i2)
  | _ ->
      let b1 = big_int_of_cilint c1 in
      let b2 = big_int_of_cilint c2 in 
      let rec loop b1 b2 mul acc =
	if nobits b1 && nobits b2 then
	  (* Once we only have all-0/all-1 values left, we can find whether
	     the infinite high-order bits are all-0 or all-1 by checking the
	     behaviour of op on b1 and b2. *)
	  if op (int_of_big_int b1) (int_of_big_int b2) = 0 then
	    acc
	  else
	    sub_big_int acc mul
	else
	  let hi1, lo1 = quomod_big_int b1 b30 in
	  let hi2, lo2 = quomod_big_int b2 b30 in
	  let lo = op (int_of_big_int lo1) (int_of_big_int lo2) in
	  loop hi1 hi2 (mult_big_int mul b30) 
	    (add_big_int acc (mult_big_int mul (big_int_of_int lo)))
      in cilint_of_big_int (loop b1 b2 unit_big_int zero_big_int)

let logand_cilint = logop (land)
let logor_cilint = logop (lor)
let logxor_cilint = logop (lxor)

let shift_right_cilint (c1:cilint) (n:int) : cilint = 
  match c1 with
  | Small i -> Small (i asr n)
  | Big b -> cilint_of_big_int (div_big_int b (power_int_positive_int 2 n))

let shift_left_cilint (c1:cilint) (n:int) : cilint = 
  cilint_of_big_int (mult_big_int (big_int_of_cilint c1) (power_int_positive_int 2 n))

let lognot_cilint (c1:cilint) : cilint = 
  match c1 with
  | Small i -> Small (lnot i)
  | Big b -> Big (pred_big_int (minus_big_int b))

let truncate_signed_cilint (c:cilint) (n:int) : cilint * truncation =
  match c with
  | Small i when n >= Nativeint.size - 1 -> Small i, NoTruncation
  | Small i when n < Nativeint.size - 2 -> 
      let max = 1 lsl (n - 1) in
      let truncmax = 1 lsl n in
     let bits = i land (truncmax - 1) in
      let tval = 
	if bits < max then
	  bits
	else
	  bits - truncmax
      in
      let trunc = 
	if i > max || i < -max then
	  if i > truncmax then 
	    BitTruncation
	  else
	    ValueTruncation
	else
	  NoTruncation
      in Small tval, trunc
  | _ ->
      let b = big_int_of_cilint c in
      let max = power_int_positive_int 2 (n - 1) in
      let truncmax = power_int_positive_int 2 n in
      let bits = mod_big_int b truncmax in
      let tval = 
	if lt_big_int bits max then
	  bits
	else
	  sub_big_int bits truncmax
      in
      let trunc = 
	if ge_big_int b max || lt_big_int b (minus_big_int max) then
	  if ge_big_int b truncmax then 
	    BitTruncation
	  else
	    ValueTruncation
	else
	  NoTruncation
      in cilint_of_big_int tval, trunc

let truncate_unsigned_cilint (c:cilint) (n:int) : cilint * truncation =
  match c with
  | Small i when i > 0 && n >= Nativeint.size - 2 -> Small i, NoTruncation
  | Small i when n < Nativeint.size - 2 ->
      let max = 1 lsl (n - 1) in
      let truncmax = 1 lsl n in
      let bits = i land (truncmax - 1) in
      let trunc = 
	if i > truncmax || i < 0 then
	  if i < -max then
	    BitTruncation
	  else
	    ValueTruncation
	else
	  NoTruncation
      in Small bits, trunc
  | _ ->
      let b = big_int_of_cilint c in
      let max = power_int_positive_int 2 (n - 1) in
      let truncmax = power_int_positive_int 2 n in
      let bits = mod_big_int b truncmax in
      let trunc = 
	if ge_big_int b truncmax || lt_big_int b zero_big_int then
	  if lt_big_int b (minus_big_int max) then
	    BitTruncation
	  else
	    ValueTruncation
	else
	  NoTruncation
      in cilint_of_big_int bits, trunc
	
let is_int_cilint (c:cilint) : bool = 
  match c with
  | Small _ -> true
  | Big b -> is_int_big_int b
