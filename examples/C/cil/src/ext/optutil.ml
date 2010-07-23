(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

(* Define some utilities for optimization *)
open Cil
open Pretty

module E = Errormsg

(** A normal form for expression that generalizes constant folding: *)
(*              E = n0 * E0 + n              *)
(*              where n0 and n are constants *)
type normalExp = (
        int * exp (* A scaled expression *)
      * int (* plus a constant *)
      ) option

(** A normal form for addresses that exposes the base, address and the index *)
(*              A = Base + scale * Index + offset       *)
(*              where scale and offset are constants    *)
(*                and Base is an Lval, AddrOf, StartOf  *)
(*              all arithemtic is done on integer types *)
(** We keep a normal form for addresses *)
type normalAddr = (
        exp (* The base address, a Lval, AddrOf, StartOf *)
      * int * exp (* A scale (maybe 0) times an index *)
      * int       (* An offset *)
      ) option 

let d_nexp () = function
    None -> text "NoNormExp"
  | Some (s, i, o) -> dprintf "%d*%a+%d" s d_exp i o

let d_naddr () = function
    None -> text "NoNormAddr"
  | Some (b, s, i, o) -> dprintf "%a+%d*%a+%d" d_exp b s d_exp i o


(** Multiply a normalized expression *)
let multNormalExp (ne: normalExp) (fact: int) : normalExp = 
  match ne with 
    None -> None
  | Some (s, e, o) -> Some (s * fact, e, o * fact)

(* Add two normalized expressions *)
let addNormalExp (ne: normalExp) (ne': normalExp) : normalExp = 
  match ne, ne' with
    None, _ -> None
  | _, None -> None
  | Some (s, e, o), Some (s', e', o') -> 
      if s = 0 then Some (s', e', o + o') 
      else if s' = 0 then Some (s, e, o + o') 
      else
        (* Both s and s' are non-null. Hope that e are the same *)
        if e == e' then 
          Some (s + s', e, o + o')
        else 
          None

(* Add a normal expression to a normal address *)
let addNormalAddr (na: normalAddr) (ne: normalExp): normalAddr = 
  match na, ne with 
    None, _ -> None
  | _, None -> None
  | Some (b, s, i, o), Some (s', i', o') -> begin
      match addNormalExp (Some (s, i, o)) (Some (s', i', o')) with 
        None -> None
      | Some (s'', i'', o'') -> Some (b, s'', i'', o'')
  end

(** Normalize an expression *)
let rec normalizeExp (e: exp) : normalExp = 
  match e with 
    CastE(_, e) -> normalizeExp e
  | Const(CInt64(i, _, _)) -> Some (0, zero, Int64.to_int i)
  | BinOp(PlusA, e1, e2, _) -> 
      addNormalExp (normalizeExp e1) (normalizeExp e2)
  | BinOp(MinusA, e1, e2, _) -> 
      addNormalExp (normalizeExp e1) (multNormalExp (normalizeExp e2) (-1))
  | BinOp(Mult, Const(CInt64(i, _, _)), e2, _) -> 
      multNormalExp (normalizeExp e2) (Int64.to_int i)
  | BinOp(Mult, e1, Const(CInt64(i, _, _)), _) -> 
      multNormalExp (normalizeExp e1) (Int64.to_int i)
  | SizeOf (t) -> begin
      try
        Some (0, zero, bitsSizeOf t / 8)
      with _ -> None
  end
  | SizeOfE (e) -> begin
      try
        Some (0, zero, bitsSizeOf (typeOf e) / 8)
      with _ -> None
  end
  | e -> Some (1, e, 0)

(** Normalize an address *)
let rec normalizeAddr (a: exp): normalAddr = 
  match a with 
  | CastE (_, a) -> normalizeAddr a
  | StartOf _ | Lval _ -> Some (a, 0, zero, 0)
  | BinOp((PlusPI|IndexPI), a, off, TPtr(bt, _)) -> begin
      try
        let bt_size = bitsSizeOf bt / 8 in
        addNormalAddr (normalizeAddr a) 
          (multNormalExp (normalizeExp off) bt_size)
      with _ -> None
  end
  | BinOp(MinusPI, a, off, TPtr(bt, _)) -> begin
      try
        let bt_size = bitsSizeOf bt / 8 in
        addNormalAddr (normalizeAddr a) 
          (multNormalExp (normalizeExp off) (- bt_size))
      with _ -> None
  end
  | AddrOf (h, off) -> begin
      (* Hopefully it is ...[i] *)
      let rec getHostIndex (off: offset) : (offset * exp) option = 
        match off with 
        | NoOffset -> None
        | Index(idx, NoOffset) -> Some (NoOffset, idx)
        | Field (f, off) -> begin
            match getHostIndex off with 
              None -> None
            | Some (hoff, idx) -> Some (Field(f, hoff), idx)
        end
        | Index(idx0, off) -> begin
            match getHostIndex off with 
              None -> None
            | Some (hoff, idx) -> Some (Index(idx0, hoff), idx)
        end
      in
      match getHostIndex off with 
        None -> Some (a, 0, zero, 0)
      | Some (hoff, idx) -> 
          try
            let bt_size = bitsSizeOf (typeOfLval (h, off)) / 8 in
            addNormalAddr 
              (normalizeAddr (StartOf (h, hoff)))
              (multNormalExp (normalizeExp idx) bt_size)
          with _ -> None
  end
  | _ -> None

(* For debugging 
let normalizeExp (e: exp) : normalExp = 
  let res = normalizeExp e in
  ignore (E.log "normalizeExp(%a) = %a\n" d_exp e d_nexp res);
  res

let normalizeAddr (a: exp) : normalAddr = 
  let res = normalizeAddr a in
  ignore (E.log "normalizeAddr(%a) = %a\n" d_exp a d_naddr res);
  res
*)
  
