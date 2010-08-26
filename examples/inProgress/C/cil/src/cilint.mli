(* cilint: infinite-precision, 2's complement arithmetic. *)

(** The cilint type is public and not just big_int to make life with ocamldebug
    easier. Please do not rely on this representation, use the ..._of_cilint
    functions to get at a cilint's value. *)
type cilint = Small of int | Big of Big_int.big_int

(** 0 as a cilint *)
val zero_cilint : cilint

(** 1 as a cilint *)
val one_cilint : cilint

(** Result type for truncate_... functions *)
type truncation = NoTruncation | ValueTruncation | BitTruncation

(** Truncate a cilint to an n-bit, signed 2's complement
 * integer. Returns the truncated value, and an indication of the loss
 * of precision.  NoTruncation means the truncated value = original
 * value. ValueTruncation means that truncated value <> original value,
 * but the original value was between -2^(n-1) and (2^n)-1, so no
 * "interesting" (not all-0 or all-1) bits were lost. If neither
 * condition holds, the result is BitTruncation. *)
val truncate_signed_cilint : cilint -> int -> cilint * truncation

(** Truncate a cilint to an n-bit, unsigned integer. Returns the
 * truncated value, and an indication of the loss of precision.
 * NoTruncation means the truncated value = original
 * value. ValueTruncation means that truncated value <> original value,
 * but the original value was between -2^(n-1) and (2^n)-1, so no
 * "interesting" (not all-0 or all-1) bits were lost. If neither
 * condition holds, the result is BitTruncation. *)
val truncate_unsigned_cilint : cilint -> int -> cilint * truncation

(** Negate a cilint *)
val neg_cilint : cilint -> cilint

(** Add two cilints *)
val add_cilint : cilint -> cilint -> cilint

(** Subtract two cilints *)
val sub_cilint : cilint -> cilint -> cilint

(** Multiply two cilints *)
val mul_cilint : cilint -> cilint -> cilint

(** Divide two cilints, rounding down *)
val div_cilint : cilint -> cilint -> cilint

(** Remainder for div_cilint *)
val mod_cilint : cilint -> cilint -> cilint

(** Divide two cilints, rounding towards zero *)
val div0_cilint : cilint -> cilint -> cilint

(** Remainder for div0_cilint *)
val rem_cilint : cilint -> cilint -> cilint

(** Bitwise-not a cilint *)
val lognot_cilint : cilint -> cilint

(** Bitwise-and of two cilints *)
val logand_cilint : cilint -> cilint -> cilint

(** Bitwise-or of two cilints *)
val logor_cilint : cilint -> cilint -> cilint

(** Bitwise-xor of two cilints *)
val logxor_cilint : cilint -> cilint -> cilint

(** Left-shift a cilint *)
val shift_left_cilint : cilint -> int -> cilint

(** Right-shift a cilint. Note that there's no
  shift_right_logical_cilint as that makes no sense on an infinite
  precision 2's complement integer *)
val shift_right_cilint : cilint -> int -> cilint

(** Return the cilint's value as an integer, or raise Failure if the value
    doesn't fit in an int *)
val int_of_cilint : cilint -> int

(** Return the low-order 64-bits of cilint's value as an int64. Note that
    this never fails. *)
val int64_of_cilint : cilint -> int64

(** Return the cilint's value as a big_int *)
val big_int_of_cilint : cilint -> Big_int.big_int

(** Return the cilint's value as a string *)
val string_of_cilint : cilint -> string

(** Make a cilint from an int *)
val cilint_of_int : int -> cilint

(** Make a cilint from an int64 *)
val cilint_of_int64 : int64 -> cilint

(** Make a cilint from a big_int *)
val cilint_of_big_int : Big_int.big_int -> cilint

(** Make a cilint from a string *)
val cilint_of_string : string -> cilint

(** Return true if the cilint is 0 *)
val is_zero_cilint : cilint -> bool

(** ordering function for two cilints *)
val compare_cilint : cilint -> cilint -> int

(** Return true if the cilint's value is representable in an int *)
val is_int_cilint : cilint -> bool
