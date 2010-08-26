(* bitvector.ml *)
(* Unit tests and ML implementation for some of bitvector.mli. *)

open Pretty            (* pretty printing *)


type bitvector         (* details are opaque to Ocaml *)

type t = bitvector

(* externals implemented in bitvectori.c *)
external make: int (*n*) -> bitvector = "bitvector_create"
external size: bitvector (*v*) -> int = "bitvector_length"
external copyBits: bitvector (*dest*) -> bitvector (*src*) -> unit = "bitvector_copyBits"
external clearAll: bitvector (*v*) -> unit = "bitvector_clearAll"
external test: bitvector (*v*) -> int (*n*) -> bool = "bitvector_test"
external setTo: bitvector (*v*) -> int (*n*) -> bool (*bit*) -> unit = "bitvector_setTo"
external testAndSetTo: bitvector (*v*) -> int (*n*) -> bool (*bit*) -> bool = "bitvector_testAndSetTo"
external set: bitvector (*v*) -> int (*n*) -> unit = "bitvector_set"
external clear: bitvector (*v*) -> int (*n*) -> unit = "bitvector_clear"
external unioneq: bitvector (*a*) -> bitvector (*b*) -> unit = "bitvector_unioneq"
external intersecteq: bitvector (*a*) -> bitvector (*b*) -> unit = "bitvector_intersecteq"
external complementeq: bitvector (*a*) -> unit = "bitvector_complementeq"
external count: bitvector (*v*) -> int = "bitvector_count"
external fold_left: ('a -> int -> 'a) (*f*) -> bitvector (*v*) -> 'a (*init*) -> 'a = "bitvector_fold_left"
external union_except: bitvector (*a*) -> bitvector (*b*) -> bitvector (*c*) -> bool = "bitvector_inplace_union_except"


(* ----------------- utilities ---------------- *)
let copy (src: bitvector) : bitvector =
begin
  let ret:bitvector = (make (size src)) in
  (copyBits ret src);
  ret
end


let union (a: bitvector) (b: bitvector) : bitvector =
begin
  let ret:bitvector = (copy a) in
  (unioneq ret b);
  ret
end

let intersect (a: bitvector) (b: bitvector) : bitvector =
begin
  let ret:bitvector = (copy a) in
  (intersecteq ret b);
  ret
end

let complement (a: bitvector) : bitvector =
begin
  let ret:bitvector = (copy a) in
  (complementeq ret);
  ret
end


let iter (f: int -> unit) (vec: bitvector): unit =
begin
  let wrapper () (i: int) : unit =
    (f i)
  in
  (fold_left wrapper vec ())
end


let rec d_bitvector () (vec: bitvector) : doc =
begin
  let len:int = (size vec) in
  let b:Buffer.t = (Buffer.create (len+2)) in

  (* build up the string using a Buffer *)
  (Buffer.add_char b '"');
  let rec loop (i: int) : unit =
  begin
    if (i < len) then (
      (Buffer.add_char b
        (if (test vec i) then '1' else '0'));
      (if (i mod 8 == 7) then
        (Buffer.add_char b '_'));
      (loop (i+1))
    )
    else
      ()
  end in
  (loop 0);
  (Buffer.add_char b '"');

  (* extract the built string and make a doc *)
  (text (Buffer.contents b))
end


let d_bitvector_as_set () (vec: bitvector) : doc =
begin
  if ((count vec) == 0) then
    (text "{}")
  else (
    let init:doc = (text "{") in
    let f (acc: doc) (i: int) : doc =
      if (acc == init) then
        acc ++ (num i)
      else
        acc ++ (text ",") ++ (num i)
    in
    (fold_left f vec init) ++ (text "}")
  )
end


(* ------------------ unit tests -------------------- *)
let printVec (name: string) (vec: bitvector) : unit =
begin
  ignore (printf "%s: %a %a (%d)\n" 
                 name 
                 d_bitvector vec 
                 d_bitvector_as_set vec
                 (count vec));
end


let testBitvector () : unit =
begin
  let v1:bitvector = (make 10) in
  (printVec "v1 initial       " v1);

  (set v1 4);
  (printVec "v1 with bit 4 set" v1);

  (set v1 2);
  (clear v1 4);
  (set v1 3);
  (printVec "v1 with 2,3 set  " v1);

  (try
    (set v1 (0-2));
    (failwith "should have failed")
  with Invalid_argument(s) ->
    ignore (printf "caught expected error: %s\n" s));

  (try
    (set v1 100);
    (failwith "should have failed")
  with Invalid_argument(s) ->
    ignore (printf "caught expected error: %s\n" s));

  (set v1 5);
  (set v1 7);
  (printVec "v1 with primes   " v1);


  let v2:bitvector = (make 30) in
  (printVec "v2 initial       " v2);

  (set v2 2);
  (set v2 3);
  (set v2 5);
  (set v2 7);
  (set v2 11);
  (set v2 13);
  (set v2 17);
  (set v2 19);
  (set v2 23);
  (set v2 29);
  (set v2 1);
  (printVec "v2 with primes+1 " v2);

  (clear v2 5);
  (clear v2 6);
  (clear v2 7);
  (clear v2 8);
  (clear v2 9);
  (printVec "v2, primes\\{5-9} " v2);
  
  
  (printVec "v1 | v2          " (union v1 v2));
  (printVec "v1 & v2          " (intersect v1 v2));
  (printVec "~v1              " (complement v1));
  (printVec "~v2              " (complement v2));
  
  
  let v3:bitvector = (make 64) in
  (unioneq v3 v2);
  (printVec "v3 = v2          " v3);
  (printVec "v1 | ~v3         " (union v1 (complement v3)));
  (printVec "v1 & ~v3         " (intersect v1 (complement v3)));
  (printVec "v3 | ~v1         " (union v3 (complement v1)));
  (printVec "v3 & ~v1         " (intersect v3 (complement v1)));


  (exit 0);
end


(* EOF *)
