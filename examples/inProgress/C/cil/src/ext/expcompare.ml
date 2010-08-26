(*
 *
 * Copyright (c) 2004, 
 *  Jeremy Condit       <jcondit@cs.berkeley.edu>
 *  George C. Necula    <necula@cs.berkeley.edu>
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

open Cil
open Cilint
open Cilint
open Pretty

module E = Errormsg

(**************************************************************************)
(* Helpers *)

let isConstType (t: typ) : bool =
  hasAttribute "const" (typeAttrs t)

(**************************************************************************)
(* Expression/type comparison *)

let rec compareExp (e1: exp) (e2: exp) : bool =
  (*log "CompareExp %a and %a.\n" d_plainexp e1 d_plainexp e2; *)
  e1 == e2 ||
  match e1, e2 with
  | Lval lv1, Lval lv2
  | StartOf lv1, StartOf lv2
  | AddrOf lv1, AddrOf lv2 -> compareLval lv1 lv2
  | BinOp(bop1, l1, r1, _), BinOp(bop2, l2, r2, _) ->
      bop1 = bop2 && compareExp l1 l2 && compareExp r1 r2
  | CastE(t1, e1), CastE(t2, e2) ->
      t1 == t2 && compareExp e1 e2
  | _ -> begin
      match getInteger (constFold true e1), getInteger (constFold true e2) with
        Some i1, Some i2 -> compare_cilint i1 i2 = 0
      | _ -> false
    end

and compareLval (lv1: lval) (lv2: lval) : bool =
  let rec compareOffset (off1: offset) (off2: offset) : bool =
    match off1, off2 with
    | Field (fld1, off1'), Field (fld2, off2') ->
        fld1 == fld2 && compareOffset off1' off2'
    | Index (e1, off1'), Index (e2, off2') ->
        compareExp e1 e2 && compareOffset off1' off2'
    | NoOffset, NoOffset -> true
    | _ -> false
  in
  lv1 == lv2 ||
  match lv1, lv2 with
  | (Var vi1, off1), (Var vi2, off2) ->
      vi1 == vi2 && compareOffset off1 off2
  | (Mem e1, off1), (Mem e2, off2) ->
      compareExp e1 e2 && compareOffset off1 off2
  | _ -> false

(* Remove casts that do not effect the value of the expression, such
 * as casts between different pointer types.  Of course, these casts
 * change the type, so don't use this within e.g. an arithmetic
 * expression.
 *
 * We remove casts from pointer types to unsigned int or unsigned long.
 * 
 * We also prune casts between equivalent integer types, such as a
 * difference in sign or int vs long.  But we keep other arithmetic casts,
 * since they actually change the value of the expression. *)
let rec stripNopCasts (e:exp): exp =
  match e with
    CastE(t, e') -> begin
      match unrollType (typeOf e'), unrollType t  with
        TPtr (bt1, a1), TPtr (bt2, a2)
          when isConstType bt1 = isConstType bt2 ->
          stripNopCasts e'
      (* strip casts from pointers to unsigned int/long*)
      | (TPtr _ as t1), (TInt(ik,_) as t2) 
          when bitsSizeOf t1 = bitsSizeOf t2 
            && not (isSigned ik) ->
          stripNopCasts e'
      | (TInt(ik1,_) as t1), (TInt(ik2,_) as t2)
          (* promotion when signedness is the same doesn't change value *)
          (* promotion of unsigned to signed of larger bitsize doesn't change
             value *)
          when bitsSizeOf t1 = bitsSizeOf t2 ||
               (isSigned ik1 = isSigned ik2 &&
                bitsSizeOf t1 < bitsSizeOf t2) ||
               (not(isSigned ik1) &&
                bitsSizeOf t1 < bitsSizeOf t2) -> (* Okay to strip.*)
          stripNopCasts e'
      |  _ -> e
    end
  | _ -> e

let compareExpStripCasts (e1: exp) (e2: exp) : bool =
  compareExp (stripNopCasts e1) (stripNopCasts e2)

(* A more conservative form of stripNopCasts.  Here, we only strip pointer
   casts if the base types have the same width.  Using this on the left operand
   of pointer arithmetic shouldn't change the resulting value. *)
let rec stripCastsForPtrArith (e:exp): exp =
  match e with
  | CastE(t, e') -> begin
      match unrollType (typeOf e'), unrollType t with
      (* Keep casts from void to something else.  Among other things,
       * we keep casts from void* to char* that would otherwise be
       * eliminated. *)
      | TPtr (TVoid _, _), TPtr (bt2, _) when not (isVoidType bt2) ->
          e
      (* Remove casts between pointers with equal-sized base types. *)
      | TPtr (bt1, a1), TPtr (bt2, a2) -> begin
          try
            if bitsSizeOf bt1 = bitsSizeOf bt2 &&
               isConstType bt1 = isConstType bt2 then
              stripCastsForPtrArith e'
            else 
              e
          with SizeOfError _ -> (* bt1 or bt2 is abstract; don't strip. *)
            e
        end
      (* strip casts from pointers to unsigned int/long*)
      | (TPtr _ as t1), (TInt(ik,_) as t2) 
          when bitsSizeOf t1 = bitsSizeOf t2 
            && not (isSigned ik) ->
          stripCastsForPtrArith e'
      | (TInt(ik1,_) as t1), (TInt(ik2,_) as t2) 
          (*when bitsSizeOf t1 = bitsSizeOf t2 ->*) (* Okay to strip.*)
          when bitsSizeOf t1 = bitsSizeOf t2 ||
               (isSigned ik1 = isSigned ik2 &&
                bitsSizeOf t1 < bitsSizeOf t2) ||
               (not(isSigned ik1) &&
                bitsSizeOf t1 < bitsSizeOf t2) -> (* Okay to strip.*)
          stripCastsForPtrArith e'
      |  _ -> e
    end
  | _ -> e

let compareTypes ?(ignoreSign=true)
                 ?(importantAttr : attribute -> bool = (fun _ -> true))
                 (t1 : typ) (t2 : typ) : bool =
  let typeSigNC (t : typ) : typsig =
    let attrFilter (attr : attribute) : bool =
      match attr with
      | Attr ("poly", _) (* TODO: hack hack! *)
      | Attr ("assumeconst", _)
      | Attr ("_ptrnode", _)
      | Attr ("missing_annot", _)
      | Attr ("const", [])
      | Attr ("aligned", _)
      | Attr ("volatile", [])
      | Attr ("deprecated", [])
      | Attr ("always_inline", []) -> false
      | _ -> importantAttr attr
    in
    typeSigWithAttrs ~ignoreSign (List.filter attrFilter) t
  in
  (typeSigNC t1) = (typeSigNC t2)

let compareTypesNoAttributes ?(ignoreSign=true) (t1 : typ) (t2 : typ) : bool =
  let typSig = typeSigWithAttrs ~ignoreSign:ignoreSign (fun _ -> []) in
  Util.equals (typSig t1) (typSig t2)

class volatileFinderClass br = object(self)
  inherit nopCilVisitor

  method vtype (t : typ)  =
    if hasAttribute "volatile" (typeAttrs t) then begin
      br := true;
      SkipChildren
    end
    else
      DoChildren

end

let isTypeVolatile t =
  let br = ref false in
  let vis = new volatileFinderClass br in
  ignore(visitCilType vis t);
  !br

(* strip every cast between equal pointer types *)
let rec stripCastsDeepForPtrArith (e:exp): exp =
  match e with
  | CastE(t, e') when not(isTypeVolatile t) -> begin
      let e' = stripCastsDeepForPtrArith e' in
      match unrollType (typeOf e'), unrollType t with
      (* Keep casts from void to something else.  Among other things,
       * we keep casts from void* to char* that would otherwise be
       * eliminated. *)
      | TPtr (TVoid _, _), TPtr (bt2, _) when not (isVoidType bt2) ->
          e
      (* Remove casts between pointers with equal-sized base types. *)
      | TPtr (bt1, a1), TPtr (bt2, a2) -> begin
          try
            if bitsSizeOf bt1 = bitsSizeOf bt2 &&
               isConstType bt1 = isConstType bt2 then
              e'
            else 
              CastE(t,e')
          with SizeOfError _ -> (* bt1 or bt2 is abstract; don't strip. *)
            CastE(t,e')
        end
      | _, _ -> CastE(t,e')
    end
  | UnOp(op,e,t) -> 
      let e = stripCastsDeepForPtrArith e in
      UnOp(op, e, t)
  | BinOp(MinusPP,e1,e2,t) ->
      let e1 = stripCastsDeepForPtrArith e1 in
      let e2 = stripCastsDeepForPtrArith e2 in
      if not(compareTypesNoAttributes ~ignoreSign:false 
	       (typeOf e1) (typeOf e2))
      then BinOp(MinusPP, mkCast ~e:e1 ~newt:(typeOf e2), e2, t)
      else BinOp(MinusPP, e1, e2, t)
  | BinOp(op,e1,e2,t) ->
      let e1 = stripCastsDeepForPtrArith e1 in
      let e2 = stripCastsDeepForPtrArith e2 in
      BinOp(op,e1,e2,t)
  | Lval lv -> Lval(stripCastsForPtrArithLval lv)
  | AddrOf lv -> AddrOf(stripCastsForPtrArithLval lv)
  | StartOf lv -> StartOf(stripCastsForPtrArithLval lv)
  | _ -> e

and stripCastsForPtrArithLval (lv : lval) : lval =
  match lv with
  | (Var vi, off) -> (Var vi, stripCastsForPtrArithOff off)
  | (Mem e, off) ->
      let e = stripCastsDeepForPtrArith e in
      let off = stripCastsForPtrArithOff off in
      (Mem e, off)

and stripCastsForPtrArithOff (off : offset ) : offset =
  match off with
  | NoOffset -> NoOffset
  | Field(fi, off) -> Field(fi, stripCastsForPtrArithOff off)
  | Index(e, off) ->
      let e = stripCastsDeepForPtrArith e in
      let off = stripCastsForPtrArithOff off in
      Index(e, off)

let compareExpDeepStripCasts (e1 : exp) (e2 : exp) : bool =
  compareExp (stripCastsDeepForPtrArith e1) (stripCastsDeepForPtrArith e2)


let rec compareAttrParam (ap1 : attrparam) (ap2 : attrparam) : bool =
    ap1 == ap2 ||
    match ap1, ap2 with
    | AInt i1, AInt i2 -> i1 = i2
    | AStr s1, AStr s2 -> s1 = s2
    | ACons(s1,apl1), ACons(s2,apl2) -> s1 = s2 &&
        List.length apl1 = List.length apl2 &&
        not(List.exists2 (fun ap1 ap2 -> not(compareAttrParam ap1 ap2)) apl1 apl2)
    | ASizeOf t1, ASizeOf t2 -> compareTypes t1 t2
    | ASizeOfE ap1, ASizeOfE ap2 -> compareAttrParam ap1 ap2
    | ASizeOfS ts1, ASizeOfS ts2 -> Util.equals ts1 ts2
    | AAlignOf t1, AAlignOf t2 -> compareTypes t1 t2
    | AAlignOfE ap1, AAlignOfE ap2 -> compareAttrParam ap1 ap2
    | AAlignOfS ts1, AAlignOfS ts2 -> Util.equals ts1 ts2
    | AUnOp(uop1,ap1), AUnOp(uop2,ap2) -> uop1 = uop2 && compareAttrParam ap1 ap2
    | ABinOp(bop1,ap11,ap12), ABinOp(bop2,ap21,ap22) -> bop1 = bop2 &&
        compareAttrParam ap11 ap21 && compareAttrParam ap12 ap22
    | ADot(ap1,s1), ADot(ap2,s2) -> compareAttrParam ap1 ap2 && s1 = s2
    | AStar ap1, AStar ap2 -> compareAttrParam ap1 ap2
    | AAddrOf ap1, AAddrOf ap2 -> compareAttrParam ap1 ap2
    | AIndex(ap11,ap12), AIndex(ap21,ap22) ->
        compareAttrParam ap11 ap21 && compareAttrParam ap12 ap22
    | AQuestion(ap11,ap12,ap13), AQuestion(ap21,ap22,ap23) ->
        compareAttrParam ap11 ap21 && compareAttrParam ap12 ap22 &&
        compareAttrParam ap13 ap23
    | _, _ -> false

