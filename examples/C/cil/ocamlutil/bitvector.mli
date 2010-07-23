(* bitvector.mli *)
(* This module provides efficient bitvectors.  The size of the
 * vector must be specified in advance.  The implementation
 * is in bitvectori.c and bitvector.ml. *)

type bitvector     (* details are opaque to Ocaml *)
     
type t = bitvector (* a synonim *)                            

(* Create a new bitvector with 'n' bits, all initialized to 0. *)
external make: int (*n*) -> bitvector = "bitvector_create"

(* Make a copy of 'src'. *)
val      copy: bitvector (*src*) -> bitvector


(* Query how many bits are available in 'v'; this might be more
 * than was originally requested. *)
external size: bitvector (*v*) -> int = "bitvector_length"

(* Copy the bits of 'src' into 'dest'.  If they have different
 * sizes, copy the smaller number of bits. *)
external copyBits: bitvector (*dest*) -> bitvector (*src*) -> unit = "bitvector_copyBits"

(* Set all the bits to 0. *)
external clearAll: bitvector (*v*) -> unit = "bitvector_clearAll"


(* Test bit 'n' of vector 'v'. *)
external test: bitvector (*v*) -> int (*n*) -> bool = "bitvector_test"

(* Set bit 'n' of vector 'v' to value 'bit'. *)
external setTo: bitvector (*v*) -> int (*n*) -> bool (*bit*) -> unit = "bitvector_setTo"

external testAndSetTo: bitvector (*v*) -> int (*n*) -> bool (*newval*)-> bool = "bitvector_testAndSetTo"

(* Specialized versions for setting to 0 or 1. *)
external set: bitvector (*v*) -> int (*n*) -> unit = "bitvector_set"
external clear: bitvector (*v*) -> int (*n*) -> unit = "bitvector_clear"


(* Set-like operations on set of '1' bits. *)

(* These mutate the value of 'a'. *)
external unioneq: bitvector (*a*) -> bitvector (*b*) -> unit = "bitvector_unioneq"
external intersecteq: bitvector (*a*) -> bitvector (*b*) -> unit = "bitvector_intersecteq"
external complementeq: bitvector (*a*) -> unit = "bitvector_complementeq"

(* Non-mutating versions. *)
val      union: bitvector (*a*) -> bitvector (*b*) -> bitvector
val      intersect: bitvector (*a*) -> bitvector (*b*) -> bitvector
val      complement: bitvector (*a*) -> bitvector

(* Count the number of '1' bits. *)
external count: bitvector (*v*) -> int = "bitvector_count"

(* Apply a function to each index where a '1' appears. *)
external fold_left: ('a -> int -> 'a) (*f*) -> bitvector (*v*) -> 'a (*init*) -> 'a = "bitvector_fold_left"
val      iter: (int -> unit) (*f*) -> bitvector (*v*) -> unit


(* Add to 'a' (modifying it) all the bits in 'b', except do not add
 * bits if they are also in 'c'. Return true if something was added to a. *)
external union_except: bitvector (*a*) -> bitvector (*b*) -> bitvector (*c*) -> bool = "bitvector_inplace_union_except"


(* Print a bitvector. *)
val      d_bitvector: unit -> bitvector -> Pretty.doc
val      d_bitvector_as_set: unit -> bitvector -> Pretty.doc


(* Run unit tests, then exit. *)
val      testBitvector: unit -> unit


(* EOF *)
