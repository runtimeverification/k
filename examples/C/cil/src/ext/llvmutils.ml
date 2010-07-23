(* Copyright (c) 2008 Intel Corporation 
 * All rights reserved. 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 
 * 	Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 * 	Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *     Neither the name of the Intel Corporation nor the names of its
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE INTEL OR ITS
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *)

(* General utility functions for the LLVM code generation (some of these are
   more generally useful) 
*)
open Cil
open Pretty
open List

exception Unimplemented of string
exception Bug

(* A few useful predicate / accessor functions - the accessor functions raise Bug
   when the argument isn't as expected *)

let getOption (v:'a option) : 'a = 
  match v with
  | Some x -> x
  | None -> raise Bug

(* Type predicates *)
let isFloatingType t = 
  match unrollType t with
  | TFloat _ -> true
  | _ -> false
let isSignedType t = 
  match unrollType t with
  | TInt (ik, _) -> isSigned ik
  | _ -> false
let isVaListType (t:typ) =
  match unrollType t with
  | TBuiltin_va_list _ -> true
  | _ -> false
let isCompType (t:typ) =
  match unrollType t with
  | TComp _ -> true
  | _ -> false

let defaultPromotion (t:typ) : typ option = 
  match unrollType t with
  | TFloat (FFloat, _) -> Some doubleType
  | TInt (ik, _) when bytesSizeOfInt ik < bytesSizeOfInt IInt -> Some intType
  | _ -> None

(* Extract information from types *)
let integralKind (t:typ) : ikind = 
  match unrollType t with
  | TInt (ik, _) -> ik 
  | TEnum _ -> IInt
  | _ -> IInt
let typeArrayOf (t:typ) : typ = 
  match unrollType t with
  | TArray (t, _, _) -> t
  | _ -> raise Bug
let typePointsTo (t:typ) : typ = 
  match unrollType t with
  | TPtr (t, _) -> t
  | _ -> raise Bug

let typeOfLhost (h:lhost) = 
  match h with
  | Var vi -> vi.vtype
  | Mem e -> typePointsTo (typeOf e)

(* The index of field fi within its structure *)
let fieldIndexOf (fi:fieldinfo) : int = 
  let rec indexLoop fields n = match fields with
  | [] -> raise Bug
  | fi' :: _ when fi' == fi -> n
  | _ :: fields' -> indexLoop fields' (n + 1)
  in indexLoop fi.fcomp.cfields 0

(* Reduce a constant expression to its integer value - fail if it isn't possible *)
let intConstValue (e:exp) : int64 = 
  match constFold true e with 
  | Const(CInt64(n,_,_)) -> n
  | _ -> raise Bug

(* Return the &e expression, fail if that's illegal *)
let mkAddrOfExp (e:exp) : exp =
  match e with
  | Lval lv -> mkAddrOrStartOf lv
  | _ -> raise Bug

(* Convert a CIL function signature to an LLVM type signature (as a doc string).
   'name' is the function name if any; use 'name = nil' to generate a function-type
   doc string. *)
let rec gSig (name:doc) (ret, oargs, isva, a) : doc = 
  let args = argsToList oargs in
  let parg (argname, t, _) = 
    let namedoc () = 
      (* don't print argument names in function-type doc strings *)
      if name <> nil && argname <> "" then (text " %") ++ (text argname) else nil
    in
    if isCompType t then
      (* X86: structures passed by value, using LLVM's byval annotation *)
      dprintf "%a *byval%t" dgType t namedoc
    else
      dprintf "%a%t" dgType t namedoc
  in
  let varargs () = if isva then text ", ..." else 
   match oargs with
   | Some _ -> nil
   | None -> text "..." in
  if isCompType ret then
    (* X86: structure results handled as a special first argument pointing to the
       result buffer, marked with LLVM's sret annotation *)
    let resultName () = if name <> nil then (text " %.result") else nil in
    dprintf "void %a(%a *sret%t, %a%t)" insert name dgType ret resultName (docList parg) args varargs
  else
    dprintf "%a %a(%a%t)" dgType ret insert name (docList parg) args varargs

(* Convert a CIL type 't' to an LLVM type (as a doc string) *)
and gType (t:typ) : doc = match t with
| TVoid _ -> text "void"
| TInt (ik, _) -> dprintf "i%d" (bitsSizeOf t)
| TFloat (FFloat, _) -> text "float"
| TFloat (FDouble, _) -> text "double"
| TFloat (FLongDouble, _) -> text "fp128"
| TPtr (t, _) -> 
    (* LLVM uses "i8 *" for 'void *' *)
    if isVoidType t then text "i8 *"
    else (gType t) ++ (text " *")
| TArray (t, None, _) -> (text "[ 0 x ") ++ (gType t) ++ (text "]")
| TArray (t, size, _) -> 
    let asize = try lenOfArray size with LenOfArray -> 0 in
    dprintf "[ %d x %a ]" asize dgType t
| TFun (a, b, c, d) -> gSig nil (a, b, c, d)
| TNamed (ti, _) -> gType ti.ttype
| TComp (ci, _) -> (text "%struct.") ++ (text ci.cname)
| TEnum (ei, _) -> dprintf "i%d" (bitsSizeOf t)
| TBuiltin_va_list _ -> text "i8 *"

(* Convert a CIL type 't' to an LLVM type (as a doc string), for use with dprintf's %a *)
and dgType () = gType

(* Generate an LLVM function header for function 'f' (as a doc string) *)
let gFunctionSig (fi:varinfo) : doc = 
  gSig ((text "@") ++ (text fi.vname)) (splitFunctionType fi.vtype)
(* Generate an LLVM function header for function 'f' (as a doc string), for use
   with dprintf's %a *)
let dgFunctionSig () = gFunctionSig

