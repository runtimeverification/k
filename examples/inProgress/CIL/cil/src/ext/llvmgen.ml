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

open Cil
open List
open Pretty
open Printf
open Llvmutils
open Expcompare
module H = Hashtbl
module S = String

exception NotConstant

(* Types used to represent an LLVM function body, which is just a list
    of LLVM blocks (llvmBlock), where the first block is the function
    entry point. See http://llvm.org for documentation on LLVM itself.
*)
type llvmBlock = {
    lblabel: string; (* unique label identifying this block *)
    mutable lbbody: llvmInstruction list;
    mutable lbterminator: llvmTerminator;

    (* predecessor blocks, use llvmDestinations to get successors *)
    mutable lbpreds : llvmBlock list; 
  }

and llvmInstruction = {
    mutable liresult: llvmLocal option;
    liop: llvmOp;
    mutable liargs: llvmValue list;
  }

and llvmTerminator = 
  | TUnreachable
  | TDead (* not a real LLVM terminator, used to mark blocks that should be removed *)
  | TRet of llvmValue list
  | TBranch of llvmBlock
  | TCond of llvmValue * llvmBlock * llvmBlock
  | TSwitch of llvmValue * llvmBlock * (int64 * llvmBlock) list

(* Note that LLVM values are typed; use llvmTypeOf to get the type of one of these *)
and llvmValue = 
  | LGlobal of llvmGlobal
  | LLocal of llvmLocal
  | LBool of bool
  | LInt of int64 * ikind
  | LFloat of float * fkind
  | LUndef
  | LZero
  | LNull of llvmType
  | LPhi of llvmValue * llvmBlock
  | LType of llvmType
  | LGetelementptr of llvmValue list
  | LCast of llvmCast * llvmValue * llvmType
  | LBinary of llvmBinop * llvmValue * llvmValue * llvmType
  | LCmp of llvmCmp * llvmValue * llvmValue
  | LFcmp of llvmFCmp * llvmValue * llvmValue
  | LSelect of llvmValue * llvmValue * llvmValue

and llvmLocal = string * llvmType
and llvmGlobal = string * llvmType

(* We just reuse CIL's type to represent LLVM types. As a result, the code below is
   not very careful in its use of llvmType vs typ. LLVM has some types that don't
   correspond well with C types (i1, a single-bit, and some vector-types), but we
   don't use the vector types and can fudge the uses of i1. *)
and llvmType = typ

and llvmOp = 
  | LIassign (* for use before SSA transformation *)
  | LIphi
  | LIgetelementptr
  | LIload 
  | LIstore
  | LIcall
  | LIalloca
  | LIbinary of llvmBinop
  | LIcmp of llvmCmp
  | LIfcmp of llvmFCmp
  | LIselect
  | LIcast of llvmCast
  | LIva_arg

and llvmBinop =
  | LBadd
  | LBsub
  | LBmul
  | LBudiv
  | LBsdiv
  | LBfdiv
  | LBurem
  | LBsrem
  | LBfrem
  | LBshl
  | LBlshr
  | LBashr
  | LBand
  | LBor
  | LBxor

and llvmCmp = 
  | LCeq
  | LCne
  | LCslt
  | LCult
  | LCsle
  | LCule
  | LCsgt
  | LCugt
  | LCsge
  | LCuge

and llvmFCmp = 
  | LCFoeq
  | LCFone
  | LCFolt
  | LCFole
  | LCFogt
  | LCFoge
  | LCFord
  | LCFueq
  | LCFune
  | LCFult
  | LCFule
  | LCFugt
  | LCFuge

and llvmCast = 
  | LAtrunc
  | LAzext
  | LAsext
  | LAuitofp
  | LAsitofp
  | LAfptoui
  | LAfptosi
  | LAfptrunc
  | LAfpext
  | LAinttoptr
  | LAptrtoint
  | LAbitcast

let binopName op = match op with
| LBadd -> "add"
| LBsub -> "sub"
| LBmul -> "mul"
| LBudiv -> "udiv"
| LBsdiv -> "sdiv"
| LBfdiv -> "fdiv"
| LBurem -> "urem"
| LBsrem -> "srem"
| LBfrem -> "frem"
| LBshl -> "shl"
| LBlshr -> "lshr"
| LBashr -> "ashr"
| LBand -> "and"
| LBor -> "or"
| LBxor -> "xor"

and cmpName op = match op with
| LCeq -> "eq"
| LCne -> "ne"
| LCslt -> "slt"
| LCult -> "ult"
| LCsle -> "sle"
| LCule -> "ule"
| LCsgt -> "sgt"
| LCugt -> "ugt"
| LCsge -> "sge"
| LCuge -> "uge"
      
and fcmpName op = match op with
| LCFoeq -> "oeq"
| LCFone -> "one"
| LCFolt -> "olt"
| LCFole -> "ole"
| LCFogt -> "ogt"
| LCFoge -> "oge"
| LCFord -> "ord"
| LCFueq -> "ueq"
| LCFune -> "une"
| LCFult -> "ult"
| LCFule -> "ule"
| LCFugt -> "ugt"
| LCFuge -> "uge"
      
and castName op = match op with
| LAtrunc -> "trunc"
| LAzext -> "zext"
| LAsext -> "sext"
| LAuitofp -> "uitofp"
| LAsitofp -> "sitofp"
| LAfptoui -> "fptoui"
| LAfptosi -> "fptosi"
| LAfptrunc -> "fptrunc"
| LAfpext -> "fpext"
| LAinttoptr -> "inttoptr"
| LAptrtoint -> "ptrtoint"
| LAbitcast -> "bitcast"

(* Some common LLVM types *)
let i1Type = voidType (* this could be made into a real, distinct type *)
let i32Type = TInt(intKindForSize 4 false, [])
let i8starType = charPtrType

(* Return the type of LLVM value 'v' *)
let rec llvmTypeOf (v:llvmValue) : llvmType = match v with
| LGlobal (_, t) -> TPtr(t, []) (* global LLVM symbols are pointers to the global's location *)
| LLocal (_, t) -> t
| LType t -> t
| LInt (_, ik) -> TInt(ik, [])
| LFloat (_, fk) -> TFloat(fk, [])
(* To understand getelementptr, please see the LLVM documentation (in brief, the first
   argument is a pointer, the 2nd is an index for that pointer, and subsequent arguments
   access embedded arrays and fields, and the result is a pointer to the referenced
   location) *)
| LGetelementptr [ base ] -> llvmTypeOf base
| LGetelementptr (base :: index :: path) ->
    let accessed (t:llvmType) (v:llvmValue) : llvmType = 
      match v with
      | LInt(i, _) -> begin
	  match unrollType t with
	  | TArray (t, _, _) -> t
	  | TComp (ci, _) ->
	      let field = nth ci.cfields (Int64.to_int i) in
	      field.ftype
	  | _ -> raise Bug
      end
      | _ -> raise Bug
    in 
    let t = fold_left accessed (typePointsTo (llvmTypeOf base)) path in
    TPtr(t, [])
| LCast (_, _, t) -> t
| LBool _ -> i1Type
| LNull t -> t
| LCmp _ -> i1Type
| LFcmp _ -> i1Type
| LSelect (_, v1, _) -> llvmTypeOf v1
| LBinary (_, _, _, t) -> t
| _ -> voidType

(* True if t can be the type of an LLVM local *)
let llvmLocalType (t:typ) : bool = 
  match unrollType t with
  | (TInt _ | TFloat _ | TPtr _ | TEnum _) -> true
  | _ -> false

(* True if local variable 'vi' should be represented by an LLVM local *)
let llvmUseLocal (vi:varinfo) = 
  not vi.vaddrof && llvmLocalType vi.vtype

(* True if 'vi's address is taken, and it would've been represented by
   an LLVM local if that had not been the case.
   Include hack for __builtin_va_list... *)
let llvmDoNotUseLocal (vi:varinfo) =
  vi.vaddrof && llvmLocalType vi.vtype || 
  (match unrollType vi.vtype with
   | TBuiltin_va_list _ -> true
   | _ -> false)

(* Returns the list of blocks that 'term' can branch to;
   'llvmDestinations b.lbterm' is the successors of LLVM block b *)
let llvmDestinations (term:llvmTerminator) = match term with
| TUnreachable -> []
| TDead -> []
| TRet _ -> []
| TBranch b -> [b]
| TCond (_, b1, b2) -> [b1; b2]
| TSwitch (_, defaultb, cases) -> defaultb :: (map snd cases)

(* Compare two llvmValues for equality. We can't just use = because
   that can cause an infinite loop (due to types). *)
let rec llvmValueEqual (v1:llvmValue) (v2:llvmValue) = match (v1, v2) with
| (LGlobal (name1, _), LGlobal(name2, _)) -> name1 = name2
| (LLocal (name1, _), LLocal(name2, _)) -> name1 = name2
| (LNull t1, LNull t2) -> compareTypes t1 t2
| (LPhi (v1, b1), LPhi (v2, b2)) -> llvmValueEqual v1 v2 && b1.lblabel = b2.lblabel
| (LType t1, LType t2) -> compareTypes t1 t2
| (LGetelementptr vl1, LGetelementptr vl2) -> for_all2 llvmValueEqual vl1 vl2
| (LCast (op1, v1, t1), LCast (op2, v2, t2)) -> 
    op1 = op2 && llvmValueEqual v1 v2 && compareTypes t1 t2
| (LBinary (op1, v1, w1, t1), LBinary (op2, v2, w2, t2)) ->
    op1 = op2 && llvmValueEqual v1 v2 && llvmValueEqual w1 w2 && compareTypes t1 t2
| (LCmp (op1, v1, w1), LCmp (op2, v2, w2)) ->
    op1 = op2 && llvmValueEqual v1 v2 && llvmValueEqual w1 w2
| (LFcmp (op1, v1, w1), LFcmp (op2, v2, w2)) ->
    op1 = op2 && llvmValueEqual v1 v2 && llvmValueEqual w1 w2
| (LSelect (c1, v1, w1), LSelect (c2, v2, w2)) ->
    llvmValueEqual c1 c2 && llvmValueEqual v1 v2 && llvmValueEqual w1 w2
| _ -> v1 = v2

(* Return the LLVM local for local variable 'vi' *)
let llocal (vi:varinfo) : llvmLocal = 
  (* If the variable can be stored directly in a LLVM local, do so. Otherwise,
     the LLVM local is a pointer to the actual variable (and will be stack
     allocated with alloca at the entry to the function) *)
  if llvmUseLocal vi then 
    (vi.vname, vi.vtype)
  else if llvmDoNotUseLocal vi then
    ("address." ^ vi.vname, TPtr (vi.vtype, []))
  else
    (vi.vname, TPtr (vi.vtype, []))

(* Return the LLVM global for global variable 'vi' *)
let lglobal (vi:varinfo) : llvmGlobal = 
    (vi.vname, vi.vtype)

(* Return the LLVM value representing variable 'vi' *)
let lvar (vi:varinfo) : llvmValue =
  if vi.vglob then LGlobal (lglobal vi) else LLocal (llocal vi) 

(* Return the LLVM value representing integer 'n' of integer type 't' *)
let lint (n:int) (t:typ) : llvmValue = LInt (Int64.of_int n, integralKind t)

(* Return the LLVM value corresponding to '(t)0' (this is the implicit
   comparison target in C conditions (if, &&, ||, !) *)
let lzero (t:typ) : llvmValue = 
  match unrollType t with
  | TInt (ik, _) -> LInt (Int64.zero, ik)
  | TFloat (fk, _) -> LFloat (0.0, fk)
  | TPtr _ -> LNull t
  | _ -> raise Bug

(* Build LLVM instruction 'res' = 'op' 'args' *)
let mkIns op res args = { liresult = Some res; liargs = args; liop = op }

(* Build LLVM instruction 'op' 'args' *)
let mkVoidIns op args = { liresult = None; liargs = args; liop = op }

(* Build the LLVM instruction that compares 'v' to zero, storing the boolean
   result in 'res' *)
let mkTrueIns (res:llvmLocal) (v:llvmValue) : llvmInstruction = 
  let t = llvmTypeOf v in
  if isFloatingType t then
    mkIns (LIfcmp LCFune) res [ v; lzero t ]
  else
    mkIns (LIcmp LCne) res [ v; lzero t ]

(* Build escaaped version of string s using LLVM's escaped string syntax *)
let llvmEscape (s:string) : string =
  let digit i = 
    if i < 10 then Char.chr (48 + i)
    else Char.chr (55 + i) in
  let l = S.length s in
  let b = Buffer.create (l + 2) in
  for i = 0 to l - 1 do
    let c = s.[i] in
    let cc = Char.code c in
    if cc < 32 || cc > 126 then begin
      Buffer.add_char b '\\';
      Buffer.add_char b (digit (cc / 16));
      Buffer.add_char b (digit (cc mod 16))
    end else
      Buffer.add_char b c
  done;
  Buffer.contents b

(* Negate LLVM value 'v' (must be an integer or floating constant) *)
let llvmValueNegate (v:llvmValue) : llvmValue =  match v with
| LInt (i, ik) -> LInt(Int64.sub Int64.zero i, ik)
| LFloat (f, fk) -> LFloat(-. f, fk)
| _ -> raise Bug

(* Return the LLVM cast operator for casting from 'tfrom' to 'tto *)
let llvmCastOp (tfrom:typ) (tto:typ) : llvmCast =
  if isIntegralType tfrom && isIntegralType tto then
    let frombits = bitsSizeOf tfrom 
    and tobits = bitsSizeOf tto in
    if tobits < frombits then
      LAtrunc
    else if tobits > frombits then
      if isSignedType tfrom then LAsext else LAzext
    else
      LAbitcast
  else if isIntegralType tfrom && isFloatingType tto then
    if isSignedType tfrom then LAsitofp else LAuitofp
  else if isFloatingType tfrom && isIntegralType tto then
    if isSignedType tto then LAfptosi else LAfptoui
  else if isFloatingType tfrom && isFloatingType tto then
    let frombits = bitsSizeOf tfrom 
    and tobits = bitsSizeOf tto in
    if tobits < frombits then
      LAfptrunc
    else if tobits > frombits then
      LAfpext
    else
      LAbitcast
  else if isIntegralType tfrom && isPointerType tto then
    LAinttoptr
  else if isPointerType tfrom && isIntegralType tto then
    LAptrtoint
  else if isPointerType tfrom && isPointerType tto then
    LAbitcast
  else
    raise Bug

(* comments in actual definition *)
class type llvmGenerator = object
  method addString : string -> llvmGlobal
  method addWString : int64 list -> llvmGlobal
  method mkFunction : fundec -> llvmBlock list
  method mkConstant : constant -> llvmValue
  method mkConstantExp : exp -> llvmValue

  method printGlobals : unit -> doc
  method printBlocks : unit -> llvmBlock list -> doc
  method printValue : unit -> llvmValue -> doc
  method printValueNoType : unit -> llvmValue -> doc
end

(* An object that generates code for CIL function bodies and initializers, while
   keeping track of string constants *)
class llvmGeneratorClass : llvmGenerator = object (self)
  val mutable strings : (llvmGlobal * string) list = []
  val mutable wstrings : (llvmGlobal * int64 list) list = []
  val mutable nextGLabel = 0

  (* A zero of pointer size *)
  val lzerop = lzero !upointType

   (* LLVM intrinsics, in doc string and LLVM value form. 
      The doc strings could be generated from the LLVM values *)
  val intrinsics = 
    (text "declare void @llvm.memcpy.i32(i8*, i8*, i32, i32) nounwind\n") ++
    (text "declare void @llvm.va_start(i8*)\n") ++
    (text "declare void @llvm.va_copy(i8*, i8*)\n") ++
    (text "declare void @llvm.va_end(i8*)\n") 

  val intrinsic_memcpy : llvmValue =
    let a t = ("", t, []) in
    let args = [ a i8starType; a i8starType; a i32Type; a i32Type ] in
    let t = TFun(voidType, Some args, false, []) in
    LGlobal ("llvm.memcpy.i32", t)
  val intrinsic_va_start : llvmValue =
    let a t = ("", t, []) in
    let t = TFun(voidType, Some [ a i8starType ], false, []) in
    LGlobal ("llvm.va_start", t)
  val intrinsic_va_end : llvmValue =
    let a t = ("", t, []) in
    let t = TFun(voidType, Some [ a i8starType ], false, []) in
    LGlobal ("llvm.va_end", t)
  val intrinsic_va_copy : llvmValue =
    let a t = ("", t, []) in
    let t = TFun(voidType, Some [ a i8starType; a i8starType ], false, []) in
    LGlobal ("llvm.va_copy", t)

  (* This gets set to a mapping from gcc's to LLVM's vararg intrinsics *)
  val mutable vaIntrinsics = []

  (* Return a new global label *)
  method private newGLabel () : string = 
    let nglabel = sprintf ".G%d" nextGLabel in
    nextGLabel <- nextGLabel + 1;
    nglabel

  (* Record a new string and return the global value that references it *)
  method addString (s:string) : llvmGlobal = 
    let reals = s ^ "\000" in (* CIL strings are missing the trailing nul *)
    let strt = TArray(charType, Some (kinteger IInt (S.length reals)), []) in
    let g = (self#newGLabel (), strt) in
    strings <- (g, reals) :: strings;
    g

  (* Record a new wide string and return the global value that references it *)
  method addWString (ws:int64 list) : llvmGlobal = 
    let realws = ws @ [ Int64.zero ] in (* CIL strings are missing the trailing nul *)
    let wstrt = TArray(!wcharType, Some (kinteger IInt (length realws)), []) in
    let g = (self#newGLabel (), wstrt) in
    wstrings <- (g, realws) :: wstrings;
    g

  (* Print all global symbols and intrinsics used in the functions and
     constant expressions seen so far *)
  method printGlobals () : doc = 
    let p1s ((glabel, t), s) = (* print string def *)
      dprintf "@@%s = internal constant %a c\"%s\"\n" glabel dgType t (llvmEscape s)
    and p1ws ((glabel, t), ws) = (* print wide string def *)
      let value wc = LInt (wc, !wcharKind) in
      dprintf "@@%s = internal constant %a [ %a ]\n" glabel dgType t 
	(d_list ", " self#printValue) (map value ws)
    in intrinsics ++ 
      (fold_left (++) nil (map p1s strings)) ++
      (fold_left (++) nil (map p1ws wstrings))

  (* Print an LLVM value without it's associated LLVM type *)
  method printValueNoType () (v:llvmValue) : doc = 
    match v with
    | LGlobal (s,t) -> dprintf "@@%s" s
    | LLocal (s,t) -> dprintf "%%%s" s
    | LBool true -> text "true"
    | LBool false -> text "false"
    | LInt (n,_) -> d_int64 n
    | LFloat (f,_) -> text (sprintf "%.20e" f)
    | LUndef -> text "undef"
    | LZero -> text "zeroinitializer"
    | LNull _ -> text "null"
    | LGetelementptr vl -> dprintf "getelementptr(%a)" (d_list ", " self#printValue) vl
    | LCast (op, v, t) -> dprintf "%s(%a to %a)" (castName op) self#printValue v dgType t
    | LBinary (op, v1, v2, _) -> dprintf "%s(%a, %a)" (binopName op) self#printValue v1 self#printValue v2
    | LCmp (op, v1, v2) -> dprintf "icmp %s (%a, %a)" (cmpName op) self#printValue v1 self#printValue v2
    | LFcmp (op, v1, v2) -> dprintf "fcmp %s (%a, %a)" (fcmpName op) self#printValue v1 self#printValue v2
    | LSelect (c, v1, v2) -> dprintf "select (%a, %a, %a)" self#printValue c self#printValue v1 self#printValue v2
    | LPhi (v,b) -> dprintf "[ %a, %%%s ]" self#printValueNoType v b.lblabel
    | LType _ -> nil

  (* Print an LLVM value prefixed by it's LLVM type *)
  method printValue () (v:llvmValue) : doc =
    let vdoc = self#printValueNoType () v in
    let t = llvmTypeOf v in
    if t <> voidType then
      (gType t) ++ (text " ") ++ vdoc
    else
      vdoc

  (* Print an LLVM block list *)
  method printBlocks () (bl:llvmBlock list) : doc =
    let rec llvmPrintIns (i:llvmInstruction) : doc =  
      let (ddest, dtype) = match i.liresult with
      | Some (s, t) -> (dprintf "%%%s = " s, t)
      | None -> (nil, voidType)
      and p n () = self#printValue () (nth i.liargs n) (* print nth arg *)
      and pnt n () = self#printValueNoType () (nth i.liargs n) (* print nth arg w/o type *)
      in ddest ++ match i.liop with 
      | LIassign -> dprintf "[%t]\n" (p 0)
      | LIload -> dprintf "load %t\n" (p 0)
      | LIstore -> dprintf "store %t, %t\n" (p 0) (p 1)
      | LIcall -> dprintf "call %t(%a)\n" (p 0) (d_list ", " self#printValue) (tl i.liargs)
      | LIbinary op -> dprintf "%s %t, %t\n" (binopName op) (p 0) (pnt 1)
      | LIcmp op -> dprintf "icmp %s %t, %t\n" (cmpName op) (p 0) (pnt 1)
      | LIfcmp op -> dprintf "fcmp %s %t, %t\n" (fcmpName op) (p 0) (pnt 1)
      | LIselect ->  dprintf "select i1 %t, %t, %t\n" (pnt 0) (p 1) (p 2)
      | LIva_arg ->  dprintf "va_arg %t, %t\n" (p 0) (p 1)
      | LIcast op -> dprintf "%s %t to %t\n" (castName op) (p 0) (p 1)
      | LIphi -> dprintf "phi %a %a\n" dgType dtype (d_list ", " self#printValue) i.liargs
      | LIgetelementptr -> dprintf "getelementptr %a\n" (d_list ", " self#printValue) i.liargs
      | LIalloca -> dprintf "alloca %a\n" (d_list ", " self#printValue) i.liargs

    and llvmPrintTerm (term:llvmTerminator) : doc = 
      match term with
      | TUnreachable -> text "unreachable\n"
      | TDead -> text "unreachable\n"
      | TBranch b -> dprintf "br label %%%s\n" b.lblabel
      | TCond (v, b1, b2) -> dprintf "br i1 %a, label %%%s, label %%%s\n"
	    self#printValueNoType v b1.lblabel b2.lblabel
      | TSwitch (v, def, cases) ->
	  let printOneCase () (n, b) = 
	    dprintf "%a %a, label %%%s" dgType (llvmTypeOf v) f_int64 n b.lblabel in
	  dprintf "switch %a, label %%%s [ %a ]\n" self#printValue v def.lblabel
	    (d_list " " printOneCase) cases
      | TRet [] -> text "ret void\n"
      | TRet rl -> dprintf "ret %a\n" (d_list ", " self#printValue) rl

    and llvmPrint1 (b:llvmBlock) : doc = 
      let label = 
	if b.lblabel <> "" then dprintf "%s:\n" b.lblabel
	else nil
      and body = fold_left (++) nil (map llvmPrintIns b.lbbody)
      and term = llvmPrintTerm b.lbterminator in
      label ++ (indent 8 (body ++ term))

    in fold_left (++) nil (map llvmPrint1 bl)

  (* Build the LLVM value for CIL constant 'c' *)
  method mkConstant (c:constant) : llvmValue = 
    match c with
    | CInt64 (i, ik, _) -> LInt (i, ik)
    | CStr s -> LGetelementptr [ LGlobal (self#addString s); lzerop; lzerop ]
    | CWStr ws -> LGetelementptr [ LGlobal (self#addWString ws); lzerop; lzerop ]
    | CChr c -> LInt (Int64.of_int (Char.code c), IInt)
    | CReal (f, fk, _) -> LFloat (f, fk)
    | CEnum (e, _, ei) -> LInt (intConstValue e, ei.ekind)

  (* Build the LLVM value for CIL constant expression 'e' - this includes constant
     lvalues like &s[3].a.b[2].c which CIL doesn't constant fold *)
  method mkConstantExp (e:exp) : llvmValue = 
    (* This is a simplified, restricted version of the code generation case... *)
    let rec accessPath (o:offset) : llvmValue list = 
      match o with
      | NoOffset -> []
      | Field (fi, o') -> (lint (fieldIndexOf fi) i32Type) :: accessPath o'
      | Index (e, o') -> (self#mkConstantExp e) :: accessPath o'

    and iStartOf (h, o) : llvmValue = 
      let opath = (accessPath o) @ [ lzerop ] in
      match h with
      | Var vi when vi.vglob -> LGetelementptr (lvar vi :: lzerop :: opath)
      | _ -> raise NotConstant

    and iAddrOf (h, o) : llvmValue = 
      let opath = accessPath o in
      match h with
      | Var vi when vi.vglob -> 
	  if opath = [] then
	    lvar vi
	  else
	    LGetelementptr (lvar vi :: lzerop :: opath)
      | _ -> raise NotConstant

    and plusPI (p:llvmValue) (offset:llvmValue) : llvmValue = 
      (* Add 'offset' to the last offset in getelementptr value 'p' *)
      match (p, offset) with
      | (LGetelementptr vl, LInt(i, _)) ->
	  (* The current offset is at the end of the getelementptr value... *)
	  let rev_vl = rev vl in
	  let newoffset = 
	    match hd rev_vl with
	    | LInt(j, jk) -> LInt(Int64.add i j, jk)
	    | _ -> raise NotConstant
	  in
	  LGetelementptr (rev (newoffset :: tl rev_vl))
      | _ -> raise NotConstant

    and minusPI (p:llvmValue) (offset:llvmValue) = plusPI p (llvmValueNegate offset)

    and mkConstantCast (v:llvmValue) (tto:typ) : llvmValue = 
      let castop = llvmCastOp (llvmTypeOf v) tto in
      LCast (castop, v, tto)

    and iCast (tto:typ) (e:exp) : llvmValue = 
      let castop = llvmCastOp (typeOf e) tto in
      LCast (castop, (self#mkConstantExp e), tto)

    and iUnop op (e:exp) (t:typ) : llvmValue = 
      let v = self#mkConstantExp e in
      let targ = typeOf e in
      match op with 
      | Neg -> LBinary (LBsub, lzero targ, v, t)
      | BNot -> LBinary (LBxor, v, lint (-1) targ, t)
      | LNot -> 
	  let t = llvmTypeOf v in
	  let cond = 
	    if isFloatingType t then
	      LFcmp (LCFune, v, lzero t)
	    else
	      LCmp (LCne, v, lzero t)
	  in LSelect (cond, lzero t, lint 1 t)

    and iBinop op (e1:exp) (e2:exp) (t:typ) : llvmValue = 
      let v1 = self#mkConstantExp e1 in
      let v2 = self#mkConstantExp e2 in
      let targ1 = typeOf e1 in
      (* generate constant for an arithmetic operator *)
      let arith op = LBinary (op, v1, v2, t) in
      (* generate constant for a comparison operator *)
      let compare sop uop fop = 
	let cond = 
	  if isIntegralType targ1 then 
	    if isSignedType targ1 then LCmp (sop, v1, v2) 
	    else LCmp (uop, v1, v2)
	  else LFcmp (fop, v1, v2)
	in LSelect(cond, lint 1 t, lint 0 t)
      in
      match op with 
      | PlusA -> arith LBadd
      | MinusA -> arith LBsub
      | (PlusPI | IndexPI) -> plusPI v1 v2
      | MinusPI -> minusPI v1 v2
      | MinusPP -> 
          let asint1 = mkConstantCast v1 t in
          let asint2 = mkConstantCast v2 t in
	  let elemsize = bitsSizeOf (typePointsTo targ1) / 8 in
	  let diff = LBinary (LBsub, asint1, asint2, t) in
	  LBinary (LBsdiv, diff, lint elemsize t, t)
      | Mult -> arith LBmul
      | Div -> 
	  let op = 
	    if isIntegralType t then
	      if isSignedType t then LBsdiv else LBudiv
	    else LBfdiv
	  in arith op
      | Mod -> arith (if isSignedType t then LBsrem else LBurem)
      | Shiftlt -> arith LBshl
      | Shiftrt -> arith (if isSignedType t then LBashr else LBlshr)
      | BAnd -> arith LBand
      | BOr -> arith LBor
      | BXor -> arith LBxor
            (* for floating point, llvm-gcc believes in unordered !=, ordered 
	       everything else *)
      | Lt -> compare LCslt LCult LCFolt
      | Gt -> compare LCsgt LCugt LCFogt
      | Le -> compare LCsle LCule LCFole
      | Ge -> compare LCsge LCuge LCFoge
      | Eq -> compare LCeq LCeq LCFoeq
      | Ne -> compare LCne LCne LCFune
      | LAnd -> raise (Unimplemented "LAnd") (* not normally used by CIL *)
      | LOr -> raise (Unimplemented "Lor") (* not normally used by CIL *)

     (* Handle all the expressions that can actually occur in a constant or
	constant lvalue *)
    in match constFold true e with
    | Const c -> self#mkConstant c
    | CastE (t, e) -> iCast t e
    | StartOf lv -> iStartOf lv
    | AddrOf lv -> iAddrOf lv
    | UnOp (op, e, t) -> iUnop op e t
    | BinOp (op, e1, e2, t) -> iBinop op e1 e2 t
    | _ -> raise NotConstant

  (* Generate LLVM code for function 'f'.
     Note: this code assumes that the statement ids (sid field of stmt) 
     have either not been set (< 0), or are set to unique values. After 
     mkFunction returns, the statement ids will have unique positive 
     values. *)
  method mkFunction (f:fundec) : llvmBlock list = 
    (* Set up the GCC vararg intrinsic mapping (once) *)
    if vaIntrinsics = [] then
      vaIntrinsics <- [ "__builtin_va_start", intrinsic_va_start;
			"__builtin_va_copy", intrinsic_va_copy;
			"__builtin_va_end", intrinsic_va_end ];

    let blocks = ref [] in (* blocks for this function *)
    let tmp_allocas = ref [] in (* additional temporary alloca's for this function *)

    let blabels = H.create 32 in
    let nextLabel = ref 0 in
    (* Return a new label *)
    let newLabel () = 
      let nlabel = sprintf "L%d" !nextLabel in
      nextLabel := !nextLabel + 1;
      nlabel
    (* Return the unique label for statement 's' *)
    and labelOf (s:stmt) : string =
      (* Pick a new label the first time its requested *)
      if s.sid < 0 then begin
	s.sid <- !nextLabel;
	nextLabel := !nextLabel + 1
      end;
      sprintf "S%d" s.sid
    in

    (* Return the block identified by label 'label', creating an
       "empty" block if 'label' hasn't been requested before. This
       allows us to target a block X in terminators before they've
       actually been compiled: when X is finally visited, we'll call
       getNamedBlock with the same label (courtesy of labelOf), get
       the "empty" block we created earlier, and fill it in (see
       mkBlock) *)
    let rec getNamedBlock (label:string) : llvmBlock = 
      try
	H.find blabels label
      with Not_found -> (* create the empty block *)
	let nb = { lblabel = label; lbbody = []; lbterminator = TUnreachable; lbpreds = [] } in
	H.add blabels label nb;
	blocks := nb :: !blocks;
	nb 
    (* Let X be the block identified by 'label'. Sets the instructions for 
       block X to 'il' and its terminator to 'term X'. Returns X. *)
    and mkBlock (label:string) (il:llvmInstruction list) (term: llvmTerminator) : llvmBlock = 
      let nb = getNamedBlock label in
      nb.lbbody <- il;
      nb.lbterminator <- term;
      nb
    in

    let tmp = ref 0 in
    (* Return a new LLVM temporary. These must be assigned exactly once (we do
       not run the SSA transform on temporaries). *)
    let nextTemp (t:llvmType) : llvmLocal = 
      tmp := !tmp + 1;
      (sprintf ".t%d" !tmp, t)
    in

    let mkCast (v:llvmValue) (tto:typ) : llvmInstruction * llvmValue =
      let tmp = nextTemp tto in
      (mkIns (LIcast (llvmCastOp (llvmTypeOf v) tto)) tmp [ v; LType tto ], LLocal tmp)
    in

    (* Compile CIL statements to LLVM blocks - each statement becomes
       a separate LLVM block (we do some block merging as a cleanup
       pass at the end of code generation - see simplifyBlock). 

       These functions take three terminator arguments. When compiling
       a statement s, the first (XXterm) is used when s terminates
       normally, the second (XXbrk) when s terminates via a break
       statement, and the third (XXcont) when s terminates via a
       continue statement. *)

    let rec gBlock (label:string) (b:block) bterm bbrk bcont : llvmBlock =
      let rec connectStmts (s:stmt) sterm = 
	let sblock = gStmt s sterm bbrk bcont in
	TBranch sblock (* Our predecessor should branch to us... *)
      in let eblock = fold_right connectStmts b.bstmts bterm in
      mkBlock label [] eblock

    and gStmt (s:stmt) = 
      let slabel = labelOf s in
      match s.skind with
      | Instr il -> gIList slabel il
      | Return (None, _) -> gReturnVoid slabel
      | Return (Some e, _) -> gReturn slabel e
      | Goto (sref, _) -> gGoto slabel sref
      | Break _ -> gBreak slabel 
      | Continue _ -> gContinue slabel 
      | If (e, b1, b2, _) -> gIf slabel e b1 b2
      | Switch (e, b, slist, _) -> gSwitch slabel e b slist
      | Loop (b, _, _, _) -> gLoop slabel b
      | Block b -> gBlock slabel b
      | TryFinally (_, _, _) -> raise (Unimplemented "TryFinally")
      | TryExcept (_, _, _, _) -> raise (Unimplemented "TryExcept")

    and gReturnVoid (label:string) sterm sbrk scont : llvmBlock = 
      mkBlock label [] (TRet [])

    and gReturn (label:string) (e:exp) sterm sbrk scont : llvmBlock = 
      let tret = typeOf e in
        if isCompType tret then
          (* X86: structures returned by copy into distinguished first argument *)
	  let (ilret, vret) = iExp e in
	  let ilmemcpy = iMemcpy (LLocal (".result", TPtr(tret, []))) vret in
	  mkBlock label (ilret @ ilmemcpy) (TRet [])
	else
	  let retterm (v:llvmValue) : llvmTerminator = TRet [v] in
	  gExp label e retterm sbrk scont

    and gBreak (label:string) sterm sbrk scont : llvmBlock = 
      mkBlock label [] sbrk

    and gContinue (label:string) sterm sbrk scont : llvmBlock = 
      mkBlock label [] scont

    and gGoto (label:string) (sref:stmt ref) sterm sbrk scont : llvmBlock =
      let target = getNamedBlock (labelOf !sref) in
      mkBlock label [] (TBranch target)

    and gIf (label:string) (e:exp) (b1:block) (b2:block) sterm sbrk scont : llvmBlock = 
      let lb1 = gBlock (newLabel ()) b1 sterm sbrk scont in
      let lb2 = gBlock (newLabel ()) b2 sterm sbrk scont in
      let (ilcond, vcond) = iExp e in
      let istrue = nextTemp i1Type in
      let test = mkTrueIns istrue vcond in
      mkBlock label (ilcond @ [ test ]) (TCond (LLocal istrue, lb1, lb2))

    and gSwitch (label:string) (e:exp) (b:block) (slist:stmt list) sterm sbrk scont : llvmBlock = 
      ignore(gBlock (newLabel ()) b sterm sterm scont);
      let switchterm (v:llvmValue) : llvmTerminator = 
	let defblock = ref (mkBlock (newLabel ()) [] sterm) in
	let cases = ref [] in
	let addCase (target:llvmBlock) (l:label) = match l with
	| Label _ -> ()
	| Case (e, _) -> cases := (intConstValue e, target) :: !cases
	| Default _ -> defblock := target
	in iter (fun s -> iter (addCase (getNamedBlock (labelOf s))) s.labels) slist;
	TSwitch (v, !defblock, !cases)
      in 
      gExp label e switchterm sbrk scont

    and gLoop (label:string) (b:block) sterm sbrk scont : llvmBlock = 
      let loop = getNamedBlock label in
      let loopback = TBranch loop in
      gBlock label b loopback sterm loopback

    and gIList (label:string) (instrs:instr list) sterm sbrk scont =
      let il_instrs = flatten (map iIns instrs) in
      mkBlock label il_instrs sterm

    and gExp (label:string) (e:exp) (eterm:llvmValue -> llvmTerminator) ebrk econt : llvmBlock = 
      let (il,v) = iExp e in
      mkBlock label il (eterm v)

    (* Generate instructions to memcpy src to dest *)
    and iMemcpy (dest:llvmValue) (src:llvmValue) : llvmInstruction list =
      let t = typePointsTo (llvmTypeOf dest) in
      let size = lint ((bitsSizeOf t) / 8) i32Type in
      let align = lint (alignOf_int t) i32Type in
      let (idest_cast, i8dest) = mkCast dest i8starType in
      let (isrc_cast, i8src) = mkCast src i8starType in
      let imemcpy = mkVoidIns LIcall [ intrinsic_memcpy; i8dest; i8src; size; align ] in
      [ idest_cast; isrc_cast; imemcpy ]

    and iIns (i:instr) : llvmInstruction list = match i with
    | Set (lv, e, _) -> iSet lv e
    (* GCC: recognize and handle gcc's intrinsic vararg functions *)
    | Call (None, Lval(Var vi, NoOffset), args, _) 
      when mem_assoc vi.vname vaIntrinsics -> iVaIntrinsic vi.vname args
    (* GCC: recognize and handle gcc's intrinsic va_arg function *)
    | Call (None, Lval(Var vi, NoOffset), [valist; SizeOf targ; dest], _) 
      when vi.vname = "__builtin_va_arg" -> iVaArg valist targ dest
    | Call (r, fn, args, _) -> iCall r fn args
    | Asm _ -> raise (Unimplemented "Asm")

    and iSet (lv:lval) (e:exp) : llvmInstruction list = 
      let (il,v) = iExp e in
      il @ iWLval lv v

    (* Handle one of gcc's intrinsic vararg functions (va_start, va_end, va_copy) 
       by calling the corresponding LLVM intrinsic. This latter expects all
       arguments to be of type i8 *, and be the address of the va_list arguments. *)
    and iVaIntrinsic (name:string) (args:exp list) : llvmInstruction list =
      let vaExp (e:exp) = 
	let (il, v) = iExp (mkAddrOfExp e) in
        let (iv_cast, vi8) = mkCast v i8starType in
	(il @ [ iv_cast ], vi8)
      in
      let (ilargs, vargs) = split (map vaExp args) in
      let call = mkVoidIns LIcall (assoc name vaIntrinsics :: vargs) in
      (flatten ilargs) @ [ call ]

    (* Handle gcc's intrinsic va_arg function by using LLVM's va_arg instruction *)
    and iVaArg (valist:exp) (targ:typ) (dest:exp) = 
      let destlv = match dest with
      | CastE(_, AddrOf lv) -> lv
      | _ -> raise Bug in
      let (il, v) = iExp (mkAddrOfExp valist) in
      let tmpdest = nextTemp targ in
      let va_arg_ins = mkIns LIva_arg tmpdest [ v; LType targ ] in
      (* CIL doesn't insert the implicit cast to dest's type, so we do... *)
      let destt = (typeOfLval destlv) in
      if compareTypes targ destt then
	il @ (va_arg_ins :: iWLval destlv (LLocal tmpdest))
      else
        let (cast_ins, vcast) = mkCast (LLocal tmpdest) destt in 
	il @ (va_arg_ins :: cast_ins :: iWLval destlv vcast)

    and iCall (r:lval option) (fn:exp) (args:exp list) : llvmInstruction list = 
      let (ret, argst, _, _) = splitFunctionType (typeOf fn) in
      let (ilargs, vargs) = split (iArgs args (argsToList argst)) in
      let (ilfn, vfn) = iExp (mkAddrOfExp fn) in
      if isCompType ret then
        (* X86: structures returned by copy into distinguished first argument *)
	match r with
	| Some rv ->
            (* iRLval returns the pointer value when asked to read a structure *)
	    let (ilres, vresptr) = iRLval rv in
	    let call = mkVoidIns LIcall (vfn :: vresptr :: vargs) in
	    (flatten ilargs) @ ilres @ ilfn @ [ call ]
	| None ->
	    let resptr = nextTemp (TPtr(ret, [])) in
	    tmp_allocas := mkIns LIalloca resptr [ LType ret ] :: !tmp_allocas;
	    let call = mkVoidIns LIcall (vfn :: (LLocal resptr) :: vargs) in 
	    (flatten ilargs) @ ilfn @ [ call ]
      else
	match r with 
	| Some rv ->
	    let callResult = nextTemp ret in
	    let call = mkIns LIcall callResult (vfn :: vargs) in
	    (flatten ilargs) @ ilfn @ [ call ] @ iWLval rv (LLocal callResult)
	| None ->
	    let call = mkVoidIns LIcall (vfn :: vargs) in 
	    (flatten ilargs) @ ilfn @ [ call ]

    and iArgs (args:exp list) (argts: (string * typ * attributes) list) : (llvmInstruction list * llvmValue) list = 
      (* compile argument list - this would be just "map iExp", except that
	 CIL doesn't include the default promotions for varargs and oldstyle
	 functions *)
      match (args, argts) with
      | ([], []) -> []
      | (a1::args', t1::argts') -> iExp a1 :: iArgs args' argts'
      | (a1::args', []) ->
	  let t1 = typeOf a1 in
	  begin
	    match defaultPromotion t1 with
	    | Some t' -> iCast t' a1 :: iArgs args' []
	    | None -> iExp a1 :: iArgs args' []
	  end
      | _ -> raise Bug

    and iExp (e:exp) : llvmInstruction list * llvmValue = 
      try ([], self#mkConstantExp e)
      with NotConstant -> iExpNotConstant e

    and iExpNotConstant (e:exp) : llvmInstruction list * llvmValue = match e with
    | Const c -> ([], self#mkConstant c)
    | SizeOf t -> iExp (sizeOf t)
    | SizeOfE e -> iExp (sizeOf (typeOf e))
    | SizeOfStr s -> ([], LInt (Int64.of_int ((String.length s) + 1), !kindOfSizeOf))
    | AlignOf t -> ([], LInt (Int64.of_int (alignOf_int t), !kindOfSizeOf))
    | AlignOfE e -> ([], LInt (Int64.of_int (alignOf_int (typeOf e)), !kindOfSizeOf))
    | Lval lv -> iRLval lv
    | UnOp (op, e, t) -> iUnop op e t
    | BinOp (op, e1, e2, t) -> iBinop op e1 e2 t
    | CastE (t, e) -> iCast t e
    | AddrOf lv -> iAddrOf lv
    | StartOf lv -> iStartOf lv

    and iUnop op (e:exp) (t:typ) : llvmInstruction list * llvmValue = 
      let (il,v) = iExp e in
      let targ = typeOf e in
      let res = nextTemp t in
      let ins = 
	match op with 
	| Neg -> [ mkIns (LIbinary LBsub) res [ lzero targ; v ] ]
	| BNot -> [ mkIns (LIbinary LBxor) res [ v; lint (-1) targ ] ]
	| LNot -> 
	    let istrue = nextTemp i1Type in
	    [ mkTrueIns istrue v;
	      mkIns LIselect res [ LLocal istrue; lzero t; lint 1 t ] ]
      in (il @ ins, LLocal res)

    and iBinop op (e1:exp) (e2:exp) (t:typ) : llvmInstruction list * llvmValue = 
      let (il1,v1) = iExp e1 in
      let (il2,v2) = iExp e2 in
      let targ1 = typeOf e1 in
      let targ2 = typeOf e2 in
      let res = nextTemp t in
      (* generate code for an arithmetic operator *)
      let arith op = [ mkIns (LIbinary op) res [ v1; v2 ] ] in
      (* generate code for a comparison operator *)
      let compare sop uop fop = 
	let cmpop = 
	  if isIntegralType targ1 then 
	    if isSignedType targ1 then LIcmp sop else LIcmp uop
	  else LIfcmp fop
	in
	let istrue = nextTemp i1Type in
	[ mkIns cmpop istrue [ v1; v2 ];
	  mkIns LIselect res [ LLocal istrue; lint 1 t; lint 0 t ] ]
      in
      let il = 
	match op with 
	| PlusA -> arith LBadd
	| MinusA -> arith LBsub
	| (PlusPI | IndexPI) -> 
	    (* CIL doesn't cast the 2nd arg to int (could be viewed as a bug) *)
	    if compareTypesNoAttributes targ2 intType then
	      [ mkIns LIgetelementptr res [ v1; v2 ] ]
	    else
	      let (icast, v2') = mkCast v2 intType in
	      [ icast; mkIns LIgetelementptr res [ v1; v2' ] ]
	| MinusPI -> 
	    let tmp = nextTemp targ2 in
	    (* CIL doesn't cast the 2nd arg to int (could be viewed as a bug) *)
	    if compareTypesNoAttributes targ2 intType then
	      [ mkIns (LIbinary LBsub) tmp [ lzero targ2; v2 ];
		mkIns LIgetelementptr res [ v1; LLocal tmp ] ]
	    else
	      let (icast, v2') = mkCast v2 intType in
	      [ icast; mkIns (LIbinary LBsub) tmp [ lzero targ2; v2' ];
		mkIns LIgetelementptr res [ v1; LLocal tmp ] ]
	| MinusPP -> 
            let (cast1_ins, asint1) = mkCast v1 t in
            let (cast2_ins, asint2) = mkCast v2 t in
	    let diff = nextTemp t in
	    let elemsize = bitsSizeOf (typePointsTo targ1) / 8 in
	    [ cast1_ins; cast2_ins; 
	      mkIns (LIbinary LBsub) diff [ asint1; asint2 ];
	      mkIns (LIbinary LBsdiv) res [ LLocal diff; lint elemsize t ] ]
	| Mult -> arith LBmul
	| Div -> 
	    let op = 
	      if isIntegralType t then
		if isSignedType t then LBsdiv else LBudiv
	      else LBfdiv
	    in arith op
	| Mod -> arith (if isSignedType t then LBsrem else LBurem)
	| Shiftlt -> arith LBshl
	| Shiftrt -> arith (if isSignedType t then LBashr else LBlshr)
	| BAnd -> arith LBand
	| BOr -> arith LBor
	| BXor -> arith LBxor
        (* for floating point, llvm-gcc believes in unordered !=, ordered 
	   everything else *)
	| Lt -> compare LCslt LCult LCFolt
	| Gt -> compare LCsgt LCugt LCFogt
	| Le -> compare LCsle LCule LCFole
	| Ge -> compare LCsge LCuge LCFoge
	| Eq -> compare LCeq LCeq LCFoeq
	| Ne -> compare LCne LCne LCFune
	| LAnd -> raise (Unimplemented "LAnd") (* not normally used by CIL *)
	| LOr -> raise (Unimplemented "Lor") (* not normally used by CIL *)
      in (il1 @ il2 @ il, LLocal res)

    and iCast (tto:typ) (e:exp) : llvmInstruction list * llvmValue = 
      let (il, v) = iExp e in
      let (cast_ins, vc) = mkCast v tto in
      (il @ [ cast_ins ], vc)

    (* Return the instructions, getelementptr access path and result type for
       evaluating CIL access path 'o' from base type 't' *)
    and accessPath (o:offset) (t:typ) : llvmInstruction list * llvmValue list * typ = 
      match o with
      | NoOffset -> ([], [], t)
      | Field (fi, o') ->
	  let fieldIndex = fieldIndexOf fi in
	  let (ilo', opath', t') = accessPath o' fi.ftype in
	  (ilo', lint fieldIndex i32Type :: opath', t')
      | Index (e, o') ->
	  let (il, v) = iExp e in
	  let (ilo', opath', t') = accessPath o' (typeArrayOf t) in
	  (il @ ilo', v :: opath', t')

    and iLhost (h:lhost) : llvmInstruction list * llvmValue =
      match h with
      | Var vi -> ([], lvar vi)
      | Mem e -> iExp e

    and lvalPtr (h:lhost) (o:offset) : llvmInstruction list * llvmValue * typ = 
      if o = NoOffset then
	match h with
	| Var vi -> ([], lvar vi, vi.vtype)
	| Mem e -> let (il, v) = iExp e in (il, v, typePointsTo (typeOf e))
      else
	let (ilo, opath, t) = accessPath o (typeOfLhost h) in 
	let ptr = nextTemp (TPtr(t, [])) in
	let (ilh, vh) = iLhost h in
	(ilo @ ilh @ [ mkIns LIgetelementptr ptr (vh :: lzerop :: opath) ], LLocal ptr, t)

    and isSimpleLval (h:lhost) (o:offset) = 
      o = NoOffset && match h with
      | Var vi when isFunctionType vi.vtype -> true
      | Var vi when not vi.vglob && llvmUseLocal vi -> true
      | _ -> false

    and varinfoOf (h:lhost) = match h with
    | Var vi -> vi
    | _ -> raise Bug

   (* Return instructions to write 'v' to lvalue '(h, o)'.
      Handling NoOffset separately makes this code clearer, as it's
      always fairly different than the offset case *)
    and iWLval (h, o) (v:llvmValue) : llvmInstruction list = 
      if isSimpleLval h o then
	[ mkIns LIassign (llocal (varinfoOf h)) [ v ] ]
      else
	let (ilptr, ptr, t) = lvalPtr h o in
	if isCompType t then ilptr @ iMemcpy ptr v
	else ilptr @ [ mkVoidIns LIstore [ v; ptr ]]

   (* Read  lvalue '(h, o)', returns instructions and the LLVM value of the result.
      Handling NoOffset separately makes this code clearer, as it's
      always fairly different than the offset case *)
    and iRLval (h, o) : llvmInstruction list * llvmValue = 
      if isSimpleLval h o then
	([], lvar (varinfoOf h))
      else
	let (ilptr, ptr, t) = lvalPtr h o in
	if isCompType t then (* just return a pointer to the structure *)
	  (ilptr, ptr)
	else
	  let res = nextTemp t in
	  (ilptr @ [ mkIns LIload res [ ptr ]], LLocal res)

    (* Get a pointer to the start of an lvalue representing an array *)
    and iStartOf (h, o) : llvmInstruction list * llvmValue = 
      iAddrOf (h, (addOffset (Index (zero, NoOffset)) o))

    (* Get a pointer to lvalue '(h, o)'.
      Handling NoOffset separately makes this code clearer, as it's
      always fairly different than the offset case *)
    and iAddrOf (h, o)  : llvmInstruction list * llvmValue = 
      let (ilptr, ptr, t) = lvalPtr h o in (ilptr, ptr)

    (* stack allocate locals that aren't ssa'ed *)
    and allocateLocals (locals:varinfo list) : llvmInstruction list =
      let genLocal (il:llvmInstruction list) (vi:varinfo) = 
	if not (llvmUseLocal vi) then
	  mkIns LIalloca (llocal vi) [ LType vi.vtype ] :: il
	else
	  il
      in fold_left genLocal [] locals

    (* stack allocate and save formals whose address is taken, if they would
       normally be ssa'ed *)
    and saveFormals (formals:varinfo list) : llvmInstruction list = 
      let saveFormal (il:llvmInstruction list) (vi:varinfo) = 
	if llvmDoNotUseLocal vi then
	  let lvi = llocal vi in
	  mkIns LIalloca lvi [ LType vi.vtype ] :: 
	  mkVoidIns LIstore [ LLocal (vi.vname, vi.vtype); LLocal lvi ] :: il
	else
	  il
      in fold_left saveFormal [] formals

    (* Simplify generated blocks by removing unreachable blocks, and merging
       blocks with a single predecessor into that predecessor when possible.
       This is not strictly necessary, but makes output more readable. *)
    and simplifyBlock (b:llvmBlock) : bool =
      if b.lbterminator = TDead then 
	false
      else if length b.lbpreds = 1 then
	let pred = hd b.lbpreds in
	match pred.lbterminator with
	| TBranch _ ->
	    pred.lbbody <- pred.lbbody @ b.lbbody;
	    pred.lbterminator <- b.lbterminator;
	    b.lbbody <- [];
	    ignore(simplifyBlock pred);
	    false
	| _ -> true
      else true

    (* Change the terminator of all blocks in 'bl' not reachable from 'entry'
       to TDead, so that simplifyBlock can remove them *)
    and markReachable (entry:llvmBlock) (bl:llvmBlock list) : unit = 
      let reachable = H.create 32 in
      H.add reachable entry.lblabel true;
      let worklist = ref [ entry ] in
      let mark b = 
	if not (H.mem reachable b.lblabel) then begin
	  H.add reachable b.lblabel true;
	  worklist := b :: !worklist
	end
      in
      while !worklist <> [] do
	let work = hd !worklist in
	worklist := tl !worklist;
	iter mark (llvmDestinations work.lbterminator)
      done;
      let kill b = 
	if not (H.mem reachable b.lblabel) then b.lbterminator <- TDead
      in iter kill bl

    (* Add 'b' to the lbpreds (predecessors) set of its successors *)
    and setPredecessors (b:llvmBlock) : unit = 
      let addPred (succ:llvmBlock) =
	if not (memq b succ.lbpreds) then succ.lbpreds <- b :: succ.lbpreds
      in
      iter addPred (llvmDestinations b.lbterminator)
    in

    (*ignore(Pretty.eprintf "%a\n" (printBlock plainCilPrinter) f.sbody);*)
    let entry = gBlock "entry" f.sbody TUnreachable TUnreachable TUnreachable in
    entry.lbbody <- (saveFormals f.sformals) @ (allocateLocals f.slocals) @ !tmp_allocas @ entry.lbbody;
    markReachable entry !blocks;
    iter setPredecessors !blocks;
    blocks := filter simplifyBlock !blocks;
    (* recompute predecessors after simplification *)
    iter (fun b -> b.lbpreds <- []) !blocks;
    iter setPredecessors !blocks;
    (*fprint ~width:80 stderr (dprintf "%s\n%a" f.svar.vname self#printBlocks !blocks);*)
    !blocks
end
