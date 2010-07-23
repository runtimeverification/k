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

(** A normal form for expression that generalizes constant folding: *)
(*              E = n0 * E0 + n              *)
(*              where n0 and n are constants *)
type normalExp = (
        int * Cil.exp (* A scaled expression *)
      * int (* plus a constant *)
      ) option

(** A normal form for addresses that exposes the base, address and the index *)
(*              A = Base + scale * Index + offset       *)
(*              where scale and offset are constants    *)
(*                and Base is an Lval, AddrOf, StartOf  *)
(*              all arithemtic is done on integer types *)
(** We keep a normal form for addresses *)
type normalAddr = (
        Cil.exp (* The base address, a Lval, AddrOf, StartOf *)
      * int * Cil.exp (* A scale (maybe 0) times an index *)
      * int       (* An offset *)
      ) option 


(** Pretty printer for {!Optutil.normalExp} *)
val d_nexp: unit -> normalExp -> Pretty.doc

(** Pretty printer for {!Optutil.normalAddr} *)
val d_naddr: unit -> normalAddr -> Pretty.doc


(** Normalize an expression *)
val normalizeExp: Cil.exp -> normalExp 

(** Normalize an address *)
val normalizeAddr: Cil.exp -> normalAddr
  

(** Multiply a normalized expression by an integer factor. *)
val multNormalExp: normalExp -> int -> normalExp 

(** Add two normalized expressions *)
val addNormalExp: normalExp -> normalExp -> normalExp

(** Add a normal expression to a normal address *)
val addNormalAddr: normalAddr -> normalExp -> normalAddr

