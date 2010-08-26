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
open Pretty
module E = Errormsg

let debug : bool ref = ref false
let verbose : bool ref = ref false
let suppress : bool ref = ref false

let globals : global list ref = ref []

let curFunction : fundec ref = ref dummyFunDec
let curStmtId : int ref = ref 0

let verifiedExps : exp list ref = ref []
let verifiedArgs : exp list ref = ref []

type stats = {
  mutable numVisited : int;
  mutable visited : (exp * location) list;
  mutable failed : (exp * location) list;
  mutable verified : (exp * location) list;
}

let expStats : stats =
  { numVisited = 0; visited = []; failed = []; verified = [] }

let argStats : stats =
  { numVisited = 0; visited = []; failed = []; verified = [] }

type annot =
| AIgn
| AZero
| ANonZero
| ANonNeg
| AOne
| ANT of int
| ANTI of string * int
| ACC of int
| ACCB of string
| ACCBI of string
| AVC of string
| AVCB of string
| AVCBI of string
| AE of string
| AEI of string

type fact = string * annot

module OrderedFact = struct
  type t = fact
  let compare = compare
end
module FactSet = Set.Make(OrderedFact)

module OrderedString = struct
  type t = string
  let compare = compare
end
module StringSet = Set.Make(OrderedString)

type state = {
  mutable facts : FactSet.t;
  mutable openVars : StringSet.t;
}

type summary =
| SNone
| SInt of int
| SVar of string
| SVarOff of string * string
| SVarOffConst of string * int
| SVarMult of string * int
| SDerefVar of string
| SDerefVarOff of string * string
| SDerefVarOffConst of string * int
| SDerefVarFld of string * string
| SAddrVar of string
| SFacts of FactSet.t

let d_annot () (annot : annot) : doc =
  match annot with
  | AIgn -> text "AIgn"
  | AZero -> text "AZero"
  | ANonZero -> text "ANonZero"
  | ANonNeg -> text "ANonNeg"
  | AOne -> text "AOne"
  | ANT n -> dprintf "ANT %d" n
  | ANTI (s, n) -> dprintf "ANTI %s %d" s n
  | ACC n -> dprintf "ACC %d" n
  | ACCB s -> dprintf "ACCB %s" s
  | ACCBI s -> dprintf "ACCBI %s" s
  | AVC s -> dprintf "AVC %s" s
  | AVCB s -> dprintf "AVCB %s" s
  | AVCBI s -> dprintf "AVCBI %s" s
  | AE s -> dprintf "AE %s" s
  | AEI s -> dprintf "AEI %s" s

let d_annots () (annots : annot list) : doc =
  seq (text ", ") (d_annot ()) annots

let d_fact () ((s, a) : fact) : doc =
  dprintf "(%s %a)" s d_annot a

let d_facts () (facts : FactSet.t) : doc =
  seq (text ", ") (d_fact ()) (FactSet.elements facts)

let d_state () (state : state) : doc =
  d_facts () state.facts

let d_summary () (sum : summary) : doc =
  match sum with
  | SNone -> dprintf "SNone"
  | SInt i -> dprintf "SInt %d" i
  | SVar s -> dprintf "SVar %s" s
  | SVarOff (s1, s2) -> dprintf "SVarOff %s %s" s1 s2
  | SVarOffConst (s, i) -> dprintf "SVarOffConst %s %d" s i
  | SVarMult (s, i) -> dprintf "SVarMult %s %d" s i
  | SDerefVar s -> dprintf "SDerefVar %s" s
  | SDerefVarOff (s1, s2) -> dprintf "SDerefVarOff %s %s" s1 s2
  | SDerefVarOffConst (s, i) -> dprintf "SDerefVarOffConst %s %d" s i
  | SDerefVarFld (s1, s2) -> dprintf "SDerefVarFld %s %s" s1 s2
  | SAddrVar s -> dprintf "SAddrVar %s" s
  | SFacts _ -> dprintf "SFacts"

class cclPrinterClass = object
  inherit defaultCilPrinterClass as super

  method pAttr (attr : attribute) : doc * bool =
    match attr with
    | Attr ("out", []) -> text "OUT", false
    | Attr ("inout", []) -> text "INOUT", false
    | Attr ("ignore", []) -> text "IGN", false
    | Attr ("nullterm", []) -> text "NT", false
    | Attr ("count", [AInt n]) -> dprintf "CT(%d)" n, false
    | Attr ("count", [ACons (s, [])]) -> dprintf "CT(%s)" s, false
    | Attr ("countof", [ACons (s, [])]) -> dprintf "CTOF(%s)" s, false
    | Attr ("end", [ACons (s, [])]) -> dprintf "END(%s)" s, false
    | _ -> super#pAttr attr
end

let cclPrinter = new cclPrinterClass

let dc_type () (t : typ) : doc =
  let save = !print_CIL_Input in
  print_CIL_Input := true;
  let d = printType cclPrinter () t in
  print_CIL_Input := save;
  d

let d_stats () (s : stats) : doc =
  let numVisited = s.numVisited in
  if numVisited > 0 then begin
    let numVerified = List.length s.verified in
    let percent = numVerified * 100 / numVisited in
    dprintf "%d / %d (%d%%)" numVerified numVisited percent
  end else
    dprintf "0 / 0"

let errorTable : (int, doc) Hashtbl.t = Hashtbl.create 13

let error (fmt : ('a, unit, doc, unit) format4) : 'a =
  let f d =
    E.hadErrors := true;
    Hashtbl.add errorTable !curStmtId d
  in
  if !verbose then begin
    E.hadErrors := true;
    E.log ("%a: error: " ^^ fmt) d_loc !currentLoc
  end else
    Pretty.gprintf f ("%a: error: " ^^ fmt) d_loc !currentLoc

let warning (fmt : ('a, unit, doc, unit) format4) : 'a =
  let f d =
    Hashtbl.add errorTable !curStmtId d
  in
  if !verbose then
    E.log ("%a: warning: " ^^ fmt) d_loc !currentLoc
  else
    Pretty.gprintf f ("%a: warning: " ^^ fmt) d_loc !currentLoc

let showStmtErrors (stmt : stmt) : unit =
  List.iter
    (fun d ->
       fprint !E.logChannel 1000000 d;
       flush !E.logChannel)
    (List.rev (Hashtbl.find_all errorTable stmt.sid))

let clearStmtErrors (stmt : stmt) : unit =
  while Hashtbl.mem errorTable stmt.sid do
    Hashtbl.remove errorTable stmt.sid
  done

let clearErrors () : unit =
  Hashtbl.clear errorTable

let addVisited (s : stats) (e : exp) : unit =
  if not (List.exists (fun (e', _) -> e' == e) s.visited) then
    s.visited <- (e, !currentLoc) :: s.visited

let addFailed (s : stats) (e : exp) : unit =
  if not (List.exists (fun (e', _) -> e' == e) s.failed) then
    s.failed <- (e, !currentLoc) :: s.failed

let resetStats (s : stats) : unit =
  s.visited <- [];
  s.failed <- []

let tallyStats (s : stats) : unit =
  let newVerified =
    List.filter
      (fun (e, _) -> not (List.exists (fun (e', _) -> e' == e) s.failed))
      s.visited
  in
  s.numVisited <- (List.length s.visited) + s.numVisited;
  s.verified <- newVerified @ s.verified;
  resetStats s

let splitArrow (s : string) : string * string =
  let idx = ref (-1) in
  let len = String.length s in
  for i = 0 to len - 2 do
    if String.sub s i 2 = "->" then
      idx := i
  done;
  if !idx >= 0 then
    (String.sub s 0 !idx), (String.sub s (!idx + 2) (len - !idx - 2))
  else
    raise Not_found

let isIgnoreType (t : typ) : bool =
  hasAttribute "ignore" (typeAttrs t)

let isOutType (t : typ) : bool =
  hasAttribute "out" (typeAttrs t)

let isInOutType (t : typ) : bool =
  hasAttribute "inout" (typeAttrs t)

let isAllocator (t : typ) : bool =
  hasAttribute "cclmalloc" (typeAttrs t)

let getSizeIndex (t : typ) : int =
  try
    match List.hd (filterAttributes "cclmalloc" (typeAttrs t)) with
    | Attr ("cclmalloc", [AInt n]) -> n
    | a -> 0
  with Failure "hd" ->
    0

let listToFactSet (facts : fact list) : FactSet.t =
  List.fold_right (fun fact set -> FactSet.add fact set) facts FactSet.empty

let curVars : varinfo list ref = ref []

let clearVars () : unit =
  curVars := []

let addVar (vi : varinfo) : unit =
  if not (List.memq vi !curVars) then
    curVars := vi :: !curVars

let varNameToInfo (name : string) : varinfo option =
  try
    Some (List.find (fun vi -> vi.vname = name) !curVars)
  with Not_found ->
    None
    (*E.s (E.bug "var name not in list\n")*)

let varNameIsFS (name : string) : bool =
  match varNameToInfo name with
  | Some vi -> not vi.vaddrof
  | None -> true
  (*not (varNameToInfo name).vaddrof*)

let rec varType (name : string) : typ =
  match varNameToInfo name with
  | Some vi -> vi.vtype
  | None ->
      begin
        try
          let vname, fname = splitArrow name in
          match unrollType (varType vname) with
          | TPtr (bt, _) ->
              begin
                match unrollType bt with
                | TComp (ci, _) -> (getCompField ci fname).ftype
                | t -> E.s (E.bug "expected comp type: %a\n" d_type t)
              end
          | t -> E.s (E.bug "expected ptr type: %a\n" d_type t)
        with Not_found ->
          E.s (E.bug "unrecognized var\n")
      end
  (*(varNameToInfo name).vtype*)

let replaceName (name1 : string) (name2 : string)
                (facts : FactSet.t) : FactSet.t =
  FactSet.fold
    (fun (aname1, annot1) rest ->
       let aname2 = if aname1 = name1 then name2 else aname1 in
       let annot2 =
         match annot1 with
         | ANTI (vname1, n) when vname1 = name1 -> ANTI (name2, n)
         | AVC vname1 when vname1 = name1 -> AVC name2
         | AVCB vname1 when vname1 = name1 -> AVCB name2
         | AVCBI vname1 when vname1 = name1 -> AVCBI name2
         | ACCB vname1 when vname1 = name1 -> ACCB name2
         | ACCBI vname1 when vname1 = name1 -> ACCBI name2
         | AE vname1 when vname1 = name1 -> AE name2
         | AEI vname1 when vname1 = name1 -> AEI name2
         | ANTI _
         | AVC _
         | AVCB _
         | AVCBI _
         | ACCB _
         | ACCBI _
         | AE _
         | AEI _
         | AIgn
         | AZero
         | ANonZero
         | ANonNeg
         | AOne
         | ANT _
         | ACC _ -> annot1
       in
       FactSet.add (aname2, annot2) rest)
    facts
    FactSet.empty

let addPrefix (prefix : string) (facts : FactSet.t) : FactSet.t =
  FactSet.fold
    (fun (aname1, annot1) rest ->
       let aname2 = if aname1 <> "*" then prefix ^ aname1 else aname1 in
       let annot2 =
         match annot1 with
         | ANTI (vname1, n) when vname1 <> "*" -> ANTI (prefix ^ vname1, n)
         | AVC vname1 when vname1 <> "*" -> AVC (prefix ^ vname1)
         | AVCB vname1 when vname1 <> "*" -> AVCB (prefix ^ vname1)
         | AVCBI vname1 when vname1 <> "*" -> AVCBI (prefix ^ vname1)
         | ACCB vname1 when vname1 <> "*" -> ACCB (prefix ^ vname1)
         | ACCBI vname1 when vname1 <> "*" -> ACCBI (prefix ^ vname1)
         | AE vname1 when vname1 <> "*" -> AE (prefix ^ vname1)
         | AEI vname1 when vname1 <> "*" -> AEI (prefix ^ vname1)
         | ANTI _
         | AVC _
         | AVCB _
         | AVCBI _
         | ACCB _
         | ACCBI _
         | AE _
         | AEI _
         | AIgn
         | AZero
         | ANonZero
         | ANonNeg
         | AOne
         | ANT _
         | ACC _ -> annot1
       in
       FactSet.add (aname2, annot2) rest)
    facts
    FactSet.empty

let selectFactsEx (fn : string -> bool) (facts : FactSet.t) : FactSet.t =
  FactSet.fold
    (fun (aname, annot) rest ->
       let save =
         (fn aname) ||
         match annot with
         | ANTI (vname, _)
         | AVC vname
         | AVCB vname
         | AVCBI vname
         | ACCB vname
         | ACCBI vname
         | AE vname
         | AEI vname -> fn vname
         | AIgn
         | AZero
         | ANonZero
         | ANonNeg
         | AOne
         | ANT _
         | ACC _ -> false
       in
       if save then
         FactSet.add (aname, annot) rest
       else
         rest)
    facts
    FactSet.empty

let selectFacts (name : string) (facts : FactSet.t) : FactSet.t =
  selectFactsEx (fun name' -> name = name') facts

let getMaxFact (fn : fact -> int) (facts : FactSet.t) : int =
  FactSet.fold
    (fun fact cur -> max (fn fact) cur)
    facts
    (-1)

let getMaxACC (name : string) (facts : FactSet.t) : int =
  getMaxFact
    (fun fact ->
       match fact with
       | name', ACC n when name = name' -> n
       | _ -> -1)
    facts

let getMaxANT (name : string) (facts : FactSet.t) : int =
  getMaxFact
    (fun fact ->
       match fact with
       | name', ANT n when name = name' -> n
       | _ -> -1)
    facts

let getMaxANTI (name1 : string) (name2 : string) (facts : FactSet.t) : int =
  getMaxFact
    (fun fact ->
       match fact with
       | name1', ANTI (name2', n) when name1 = name1' && name2 = name2' -> n
       | _ -> -1)
    facts

let trimFacts (facts : FactSet.t) : FactSet.t =
  FactSet.fold
    (fun fact rest ->
       match fact with
       | name, ACC n when n < getMaxACC name facts -> rest
       | name, ANT n when n < getMaxANT name facts -> rest
       | name1, ANTI (name2, n) when n < getMaxANTI name1 name2 facts -> rest
       | _ -> FactSet.add fact rest)
    facts
    FactSet.empty

let joinFacts (facts1 : FactSet.t) (facts2 : FactSet.t) : FactSet.t =
  let facts1' = trimFacts facts1 in
  let facts2' = trimFacts facts2 in
  let join = FactSet.inter facts1' facts2' in
  FactSet.fold
    (fun fact rest ->
       let add fact' =
         FactSet.add fact' rest
       in
       match fact with
       | name, ACC n when name = "*" ->
           let m = getMaxACC name facts2' in
           if m >= 0 then
             add (name, ACC (min n m))
           else
             rest
       | name, ANT n ->
           let m = getMaxANT name facts2' in
           if m >= 0 then
             add (name, ANT (min n m))
           else
             rest
       | name1, ANTI (name2, n) ->
           let m = getMaxANTI name1 name2 facts2' in
           if m >= 0 then
             add (name1, ANTI (name2, min n m))
           else
             rest
       | _ -> rest)
    facts1'
    join

let closeFacts (facts : FactSet.t) : FactSet.t =
  (* Warning: This code may need to change for more complex closure rules. *)
  let closeAnnot (annot : annot) : annot list =
    annot ::
    match annot with
    | ANT n -> [ ACC (n + 1) ]
    | AZero -> [ ACC 1; ANT 0; ANonNeg ]
    | AOne -> [ ANonZero; ANonNeg ]
    | ACCB s -> [ ANonZero; ACCBI s ]
    | AVCB s -> [ ANonZero; AVCBI s ]
    | AE s -> [ AEI s ]
    | _ -> []
  in
  FactSet.fold
    (fun (name, annot) rest ->
       List.fold_right
         (fun annot' rest' -> FactSet.add (name, annot') rest')
         (closeAnnot annot)
         rest)
    facts
    FactSet.empty

let attrToFact (name : string) (attr : attribute) : fact option =
  match attr with
  (* My original annotations: *)
  | Attr ("ignore", []) -> Some (name, AIgn)
  | Attr ("nullterm", []) -> Some (name, ANT 0)
  | Attr ("count", [AInt n]) -> Some (name, ACC n)
  | Attr ("count", [ACons (s, [])]) -> Some (name, AVC s)
  | Attr ("countof", [ACons (s, [])]) -> Some (s, AVC name)
  | Attr ("end", [ACons (s, [])]) -> Some (name, AEI s)
  (* For compatibility with the original CCured: *)
  | Attr ("safe", []) -> Some (name, ACC 1)
  | Attr ("string", []) -> Some (name, ANT 0)
  | _ -> None

let myAttr (attr : attribute) : bool =
  match attrToFact "*" attr with
  | Some _ -> true
  | None when attr = Attr ("out", []) -> true
  | None when attr = Attr ("inout", []) -> true
  | None -> false

let attrsToFacts (name : string) (attrs : attributes) : FactSet.t =
  List.fold_right
    (fun attr rest ->
       match attrToFact name attr with
       | Some fact -> FactSet.add fact rest
       | None -> rest)
    attrs
    FactSet.empty

let typeToFactsEx (name : string) (t : typ) (extra : attributes) : FactSet.t =
  match unrollType t with
  | TArray (_, len, attrs) ->
      begin
        try
          FactSet.add
            (name, ACC (lenOfArray len))
            (attrsToFacts name (attrs @ extra))
        with LenOfArray ->
          attrsToFacts name (attrs @ extra)
      end
  | _ -> attrsToFacts name ((typeAttrs t) @ extra)

let typeToFacts (name : string) (t : typ) : FactSet.t =
  typeToFactsEx name t []

let typeToFactsPre (prefix : string) (name : string) (t : typ) : FactSet.t =
  addPrefix prefix (typeToFacts name t)

let getCompFacts (name : string) (ci : compinfo) : FactSet.t =
  List.fold_right
    (fun fld rest ->
       FactSet.union
         (addPrefix (name ^ "->") (typeToFacts fld.fname fld.ftype)) rest)
    ci.cfields
    FactSet.empty

let getFunctionFacts (t : typ) : FactSet.t * FactSet.t =
  match t with
  | TFun (rtype, args, vararg, attrs) ->
      let rec argIter i formals (accIn, accOut) =
        match formals with
        | (fName, fType, _) :: rest ->
            let fakeName =
              if fName <> "" then
                "@" ^ fName
              else
                "@$arg" ^ (string_of_int i)
            in
            let fType' =
              if isOutType fType || isInOutType fType then
                match fType with
                | TPtr (bt, _) -> bt
                | _ -> E.s (E.bug "expected ptr type\n")
              else
                fType
            in
            let newFacts =
              replaceName "*" fakeName (addPrefix "@" (typeToFacts "*" fType'))
            in
            let accIn', accOut' =
              if isOutType fType then
                accIn, FactSet.union newFacts accOut
              else if isInOutType fType then
                FactSet.union newFacts accIn, FactSet.union newFacts accOut
              else
                FactSet.union newFacts accIn, accOut
            in
            argIter (i + 1) rest (accIn', accOut')
        | [] ->
            accIn, accOut
      in
      let retFacts =
        replaceName "*" "@$ret" (addPrefix "@" (typeToFacts "*" rtype))
      in
      argIter 1 (argsToList args) (FactSet.empty, retFacts)
  | _ -> E.s (E.bug "expected function type\n")

let getVarFacts (name : string) (facts : FactSet.t) : FactSet.t =
  replaceName name "*" (selectFacts name facts)

let openVar (vname : string) (state : state) : unit =
  if not (StringSet.mem vname state.openVars) then begin
    let vi =
      match varNameToInfo vname with
      | Some vi -> vi
      | None -> E.s (E.bug "can't open non-local var\n")
    in
    let e =
      match unrollType vi.vtype with
      | TPtr _ -> Lval (Var vi, NoOffset)
      | TArray _ -> StartOf (Var vi, NoOffset)
      | _ -> E.s (E.bug "expected ptr or array type\n")
    in
    let comp =
      match unrollType (typeOfLval (Mem e, NoOffset)) with
      | TComp (ci, _) -> ci
      | t -> E.s (E.bug "expected comp type: %a\n" d_type t)
    in
    let facts = getCompFacts vname comp in
    state.facts <- FactSet.union facts state.facts;
    state.openVars <- StringSet.add vname state.openVars;
  end

let openVars (vnames : StringSet.t) (state : state) : unit =
  StringSet.iter (fun vname -> openVar vname state) vnames

let closeVar (vname : string) (state : state) : unit =
  (* TODO: check! *)
  if StringSet.mem vname state.openVars then begin
    let prefix = vname ^ "->" in
    let prefixLen = String.length prefix in
    let prefixCheck v =
      try
        String.sub v 0 prefixLen <> prefix
      with Invalid_argument _ ->
        true
    in
    state.facts <- selectFactsEx prefixCheck state.facts;
    state.openVars <- StringSet.remove vname state.openVars
  end

let closeAllVars (state : state) : unit =
  StringSet.iter (fun vname -> closeVar vname state) state.openVars

let makeState (fd : fundec) : state =
  let facts =
    List.fold_right
      (fun vi rest ->
         if not (isFunctionType vi.vtype) then
           FactSet.union (typeToFactsEx vi.vname vi.vtype vi.vattr) rest
         else
           rest)
      !curVars
      FactSet.empty
  in
  { facts = facts; openVars = StringSet.empty; }

let copyState (s : state) : state =
  { facts = s.facts; openVars = s.openVars; }

let joinStates (s1 : state) (s2 : state) : state =
  let s1' = copyState s1 in
  let s2' = copyState s2 in
  let allVars = StringSet.union s1'.openVars s2'.openVars in
  openVars allVars s1';
  openVars allVars s2';
  { facts = joinFacts (closeFacts s1'.facts) (closeFacts s2'.facts);
    openVars = allVars; }

let equalFacts (f1 : FactSet.t) (f2 : FactSet.t) : bool =
  FactSet.equal (closeFacts f1) (closeFacts f2)

let equalStates (s1 : state) (s2 : state) : bool =
  equalFacts s1.facts s2.facts

let checkCast (toFacts : FactSet.t) (fromFacts : FactSet.t) : bool =
  let toClose = closeFacts toFacts in
  let fromClose = closeFacts fromFacts in
  let join = joinFacts toClose fromClose in
  FactSet.subset toClose join

let equalTypes (t1 : typ) (t2 : typ) : bool =
  let typeSigNC (t : typ) : typsig =
    let attrFilter (attr : attribute) : bool =
      match attr with
      | Attr ("const", [])
      | Attr ("always_inline", []) -> false
      | _ -> true
    in
    typeSigWithAttrs (List.filter attrFilter) t
  in
  (typeSigNC t1) = (typeSigNC t2)

let equalBaseTypes (t1 : typ) (t2 : typ) : bool =
  equalTypes (setTypeAttrs t1 []) (setTypeAttrs t2 [])

let equalTypesNoAttrs (t1 : typ) (t2 : typ) : bool =
  let typeSigNA (t : typ) : typsig =
    typeSigWithAttrs (List.filter (fun attr -> not (myAttr attr))) t
  in
  (typeSigNA t1) = (typeSigNA t2)

class normVisitor = object
  inherit nopCilVisitor

  val mapping : (string, string) Hashtbl.t ref = ref (Hashtbl.create 1)

  method vtype (t : typ) : typ visitAction =
    match t with
    | TFun (rtype, args, vararg, attrs) ->
        let oldMapping = !mapping in
        let newMapping = Hashtbl.create 7 in
        let rec iter index args =
          match args with
          | (name, _, _) :: rest ->
              Hashtbl.add newMapping name (string_of_int index);
              iter (index + 1) rest
          | [] -> ()
        in
        iter 1 (argsToList args);
        Hashtbl.add newMapping "return" "0";
        mapping := newMapping;
        ChangeDoChildrenPost (t, (fun x -> mapping := oldMapping; x))
    | _ ->
        DoChildren

  method vattr (attr : attribute) : attribute list visitAction =
    match attr with
    | Attr ("count", [ACons (s, [])]) ->
        begin
          try
            let newAttr =
              Attr ("count", [ACons (Hashtbl.find !mapping s, [])])
            in
            ChangeTo [ newAttr ]
          with Not_found ->
            E.s (E.bug "error normalizing type")
        end
    | _ ->
        DoChildren
end

let normalizeType (t : typ) : typ =
  visitCilType (new normVisitor) t

class normVisitor2 subst = object
  inherit nopCilVisitor

  val subst = subst

  method vtype (t : typ) : typ visitAction =
    match t with
    | TFun _ -> SkipChildren
    | _ -> DoChildren

  method vattr (attr : attribute) : attribute list visitAction =
    match attr with
    | Attr (aname, [ACons (s, [])])
          when aname = "count" || aname = "countof" ->
        begin
          try
            let newAttr =
              match Hashtbl.find subst s with
              | SVar s' ->
                  [ Attr (aname, [ACons (s', [])]) ]
              | SInt i when aname = "count" ->
                  [ Attr ("count", [AInt i]) ]
              | SNone ->
                  []
              | _ ->
                  E.s (E.bug "unexpected summary\n")
            in
            ChangeTo newAttr
          with Not_found -> begin
            ignore (error "no substitution found for %s" s);
            DoChildren
          end
        end
    | _ ->
        DoChildren
end

let normalizeType2 (subst : (string, summary) Hashtbl.t) (t : typ) : typ =
  visitCilType (new normVisitor2 subst) t

let checkBaseTypes (toType : typ) (fromType : typ) : bool =
  let rec check (t1 : typ) (t2 : typ) (dontCheck : bool) : bool =
    (*ignore (E.log "checking %a = %a\n" d_type t1 d_type t2);*)
    match unrollType t1, unrollType t2 with
    | TPtr (t1', _), TPtr (t2', _) ->
        let f1 = typeToFacts "*" t1 in
        let f2 = typeToFacts "*" t2 in
        (dontCheck || equalFacts f1 f2) && check t1' t2' false
    | TFun _, TFun _ -> equalTypes (normalizeType t1) (normalizeType t2)
    | (TInt _ | TFloat _), (TInt _ | TFloat _) -> true
    | TInt _, TEnum _ -> true
    | TEnum _, TInt _ -> true
    | TInt _, TPtr _ -> true
    | TVoid _, TVoid _ -> true
    | TPtr _, TInt _ ->
        ignore (warning ("unchecked integer to pointer cast\n" ^^
                         "    to: %a\n  from: %a")
                         d_type t1 d_type t2);
        true (* TODO: improve this check *)
    | _, TVoid _
    | TVoid _, _ ->
        ignore (warning ("unchecked void cast\n" ^^
                         "    to: %a\n  from: %a")
                         d_type t1 d_type t2);
        true (* TODO: improve this check *)
    | _, _ -> equalTypes t1 t2
  in
  let res = check toType fromType true in
  (*ignore (E.log "result: %b\n" res);*)
  res

let changeFacts (fn : fact -> fact list) (facts : FactSet.t) : FactSet.t =
  FactSet.fold
    (fun fact rest ->
       List.fold_right
         (fun fact' rest' -> FactSet.add fact' rest')
         (fn fact) rest)
    (closeFacts facts)
    FactSet.empty

let changeState (fn : fact -> fact list) (state : state) : unit =
  state.facts <- changeFacts fn state.facts

let changeAnnots (fn : annot -> annot list) (facts : FactSet.t) : FactSet.t =
  FactSet.fold
    (fun (name, annot) rest ->
       List.fold_right
         (fun annot' rest' -> FactSet.add (name, annot') rest')
         (fn annot) rest)
    (closeFacts facts)
    FactSet.empty

let summaryToFacts (sum : summary) (state : state) : FactSet.t =
  match sum with
  | SNone ->
      FactSet.empty
  | SInt i ->
      let annots =
        (* TODO: refacor the following *)
        if i = 0 then
          FactSet.fold
            (fun fact rest ->
               match fact with
               | name, ANT n -> (ANTI (name, n)) :: rest
               | name, ACC n when n > i -> (ACCB name) :: rest
               | name, AVC _ -> (AVCBI name) :: rest
               | _ -> rest)
            state.facts
            [ AZero ]
        else if i = 1 then
          FactSet.fold
            (fun fact rest ->
               match fact with
               | name, ANT n when n >= i -> (ANTI (name, n - i)) :: rest
               | name, ACC n when n > i -> (ACCB name) :: rest
               | name, AVC _ -> (AVCBI name) :: rest
               | _ -> rest)
            state.facts
            [ AOne ]
        else
          FactSet.fold
            (fun fact rest ->
               match fact with
               | name, ACC n when n > i && i > 0 -> (ACCB name) :: rest
               | name, AVC _ when i > 0 -> (AVCBI name) :: rest
               | _ -> rest)
            state.facts
            [ ANonZero ]
        (* TODO: add ANonZero *)
      in
      let extra =
          FactSet.fold
            (fun fact rest ->
               match fact with
               | name, ACC n when 0 <= i && i <= n ->
                   FactSet.add (name, (AVC "*")) rest
               | _ -> rest)
            state.facts
            FactSet.empty
      in
      List.fold_right
        (fun annot rest -> FactSet.add ("*", annot) rest)
        annots extra
  | SVar vname ->
      getVarFacts vname state.facts
  | SVarOff (vname, oname) ->
      FactSet.fold
        (fun fact rest ->
           match fact with
           | vname', ANT _ when vname = vname' ->
               let maxAnti = getMaxANTI oname vname state.facts in
               if maxAnti >= 0 then
                 FactSet.add ("*", ANT maxAnti) rest
               else
                 rest
           | vname', ACC _ when vname = vname' ->
               if FactSet.mem (oname, ACCB vname) state.facts then
                 FactSet.add ("*", ACC 1) rest
               else
                 rest
           | vname', AVC _ when vname = vname' ->
               if FactSet.mem (oname, AVCB vname) state.facts then
                 FactSet.add ("*", ACC 1) rest
               else
                 rest
           | _ ->
               rest)
        state.facts
        FactSet.empty
  | SVarOffConst (vname, off) ->
      changeFacts
        (fun (vname', annot) ->
           if vname = vname' then
             match annot with
             | ACC n when n >= off -> [ ("*", ACC (n - off)); (vname, AE "*") ]
             | ANT n when n >= off -> [ ("*", ANT (n - off)); (vname, AE "*") ]
             | ANTI (s, n) when n >= off -> [ ("*", ANTI (s, n - off)) ]
             (* TODO: the following should be checked for overflow *)
             | ACCB s -> [ ("*", ANonNeg); ("*", ACCBI s) ]
             | AVCB s -> [ ("*", ANonNeg); ("*", AVCBI s) ]
             | AE s -> [ ("*", AEI s) ]
             | AZero when off = 1 -> [ ("*", AOne) ]
             | AZero when off <> 0 -> [ ("*", ANonZero) ]
             | _ -> []
           else
             [])
        state.facts
  | SVarMult _ ->
      FactSet.empty
  | SDerefVar vname
  | SDerefVarOff (vname, _)
  | SDerefVarOffConst (vname, _) ->
      let bt =
        match unrollType (varType vname) with
        | TPtr (bt, _)
        | TArray (bt, _, _) -> bt
        | _ -> E.s (E.bug "expected ptr or array type\n")
      in
      typeToFacts "*" bt
  | SDerefVarFld (vname, fname) ->
      openVar vname state;
      getVarFacts (vname ^ "->" ^ fname) state.facts
  | SAddrVar vname ->
      FactSet.singleton ("*", ACC 1)
  | SFacts facts ->
      facts

let safeDeref (facts : FactSet.t) : bool =
  FactSet.exists
    (fun fact ->
       match fact with
       | "*", ACC n when n > 0 -> true
       | _ -> false)
    (closeFacts facts)

let hasAnnot (a : annot) (facts : FactSet.t) : bool =
  FactSet.mem ("*", a) (closeFacts facts)

let summaryIsZero (sum : summary) (state : state) : bool =
  hasAnnot AZero (summaryToFacts sum state)

let summaryIsNonZero (sum : summary) (state : state) : bool =
  hasAnnot ANonZero (summaryToFacts sum state)

let rec evaluateExp (e : exp) (state : state) : summary =
  match e with
  | UnOp (op, e', _) -> SNone
  | BinOp ((PlusA | PlusPI | IndexPI), e1, e2, _) ->
      begin
        match evaluateExp e1 state, evaluateExp e2 state with
        | SVar v1, SVar v2 -> SVarOff (v1, v2)
        | SVar v1, SInt 0 -> SVar v1
        | SVar v1, SInt n -> SVarOffConst (v1, n)
        | _, _ -> SNone
      end
  | BinOp (Mult, e1, e2, _) ->
      begin
        match evaluateExp e1 state, evaluateExp e2 state with
        | SInt n1, SInt n2 -> SInt (n1 * n2)
        | SVar v1, SInt n2 -> SVarMult (v1, n2)
        | SInt n1, SVar v2 -> SVarMult (v2, n1)
        | _, _ -> SNone
      end
  | BinOp (op, e1, e2, _) -> SNone
  | AddrOf lv ->
      begin
        match evaluateLval lv state with
        | SVar vname -> SAddrVar vname
        | SDerefVar vname -> SVar vname
        | SDerefVarOff (vname, off) -> SVarOff (vname, off)
        | SDerefVarOffConst (vname, off) -> SVarOffConst (vname, off)
        | _ -> SFacts (FactSet.singleton ("*", ACC 1))
      end
  | Lval lv -> evaluateLval lv state
  | CastE (t, e') ->
      let eSum = evaluateExp e' state in
      let eFacts = summaryToFacts eSum state in
      let eType = typeOf e' in
      let tFacts = typeToFacts "*" t in
      (* TODO: NULL is defined as ((void* )0), so we hack around it... *)
      if hasAnnot AZero eFacts then
        eSum
      (* TODO: character comparisons get cast to ints, but we need to
         pass the summary through in order to recognize the conditional *)
      else if isIntegralType eType && isIntegralType t then
        eSum
      (* TODO: same with pointers *)
      else if isPointerType eType && isIntegralType t then
        eSum
      (* TODO: CIL inserts casts where toplevel annots don't match *)
      else if equalBaseTypes eType t then
        eSum
      else begin
        if not (hasAnnot AIgn tFacts) then begin
          if not (checkBaseTypes t eType) then
            ignore (error "cannot verify cast\n    to: %a\n  from: %a"
                          d_type t d_type eType);
          if not (checkCast tFacts eFacts) then
            ignore (error "cannot verify cast\n    to: %a\n  from: %a"
                          d_facts tFacts d_facts eFacts)
        end;
        SFacts tFacts
      end
  | Const (CStr s) ->
      SFacts (FactSet.singleton ("*", ANT 0))
  | Const _ ->
      begin
        match getInteger e with
        | Some i -> SInt (cilint_to_int i) (* TODO: possible bug in conv?  *)
        | None -> SNone
      end
  | SizeOf _
  | SizeOfE _
  | SizeOfStr _ ->
      let e' = constFold true e in
      begin
        match e' with
        | Const _ -> ()
        | _ -> E.s (E.bug "expected constant\n")
      end;
      evaluateExp e' state
  | AlignOf _
  | AlignOfE _ -> SNone
  | StartOf lv -> evaluateLval lv state

and evaluateLval (lv : lval) (state : state) : summary =
  match lv with
  | Var vi, NoOffset ->
      SVar vi.vname
  | Var _, _ ->
      SFacts (typeToFacts "*" (typeOfLval lv))
  | Mem e, off ->
      addVisited expStats e;
      let s = evaluateExp e state in
      if not (safeDeref (summaryToFacts s state)) then begin
        ignore (error "cannot verify dereference of %a" d_exp e);
        addFailed expStats e;
      end;
      begin
        match s, off with
        | SVar name, NoOffset -> SDerefVar name
        | SVar name, Field (fld, NoOffset) ->
            (*SDerefVarFld (name, fld.fname)*)
            let hasArrow =
              try
                name.[(String.index name '-') + 1] = '>'
              with Not_found | Invalid_argument _ ->
                false
            in
            if not hasArrow then begin
              openVar name state;
              SVar (name ^ "->" ^ fld.fname)
            end else
              SFacts (typeToFacts "*" (typeOfLval lv))
        | SVarOff (bname, oname), NoOffset -> SDerefVarOff (bname, oname)
        | SVarOffConst (name, off), NoOffset -> SDerefVarOffConst (name, off)
        | _ -> SFacts (typeToFacts "*" (typeOfLval lv))
      end

let getTypeSize (t : typ) : int =
  match getInteger (constFold true (SizeOf t)) with
  | Some i -> cilint_to_int i
  | None -> E.s (E.bug "failed to compute size of type %a\n" d_type t)

let getAllocFact (t : typ) (e : exp) (state : state) : FactSet.t * bool =
  let sz =
    match unrollType t with
    | TPtr (bt, _) -> getTypeSize bt
    | _ -> E.s (E.bug "expected ptr type\n")
  in
  let handleInt n =
    FactSet.singleton ("*", ACC (n / sz)), (n mod sz) = 0
  in
  let handleVarMult v n =
    if n >= sz then
      FactSet.singleton ("*", AVC v), (n mod sz) = 0
    else
      FactSet.empty, false
  in
  match evaluateExp e state with
  | SInt n -> handleInt n
  | SVar v -> handleVarMult v 1
  | SVarMult (v, n) -> handleVarMult v n
  | _ -> FactSet.empty, false

let analyzeCond (cond : exp) (state : state) : unit =
  let upgradeANT (n : int) (vname : string) : unit =
    changeState
      (fun (name, annot) ->
         match annot with
         | ANT m when name = vname && n = m ->
             [ (name, ANT n); (name, ANT (n + 1)) ]
         | _ -> [ (name, annot) ])
      state
  in
  let upgradeANTI (n : int) (vname : string) (sname : string) : unit =
    changeState
      (fun (name, annot) ->
         match annot with
         | ANTI (name', m) when name = vname && name' = sname && n = m ->
             [ (name, ANTI (name', n + 1)) ]
         | _ -> [ (name, annot) ])
      state
  in
  let upgradeACCBI (vname : string) (aname : string) : unit =
    changeState
      (fun (name, annot) ->
         match annot with
         | ACCBI name' when name = vname && name' = aname ->
             [ (name, ACCB name') ]
         | AZero when name = vname ->
             [ (name, annot); (name, ACCB aname) ]
         | ANonNeg when name = vname ->
             [ (name, annot); (name, ACCB aname) ]
         | _ -> [ (name, annot) ])
      state
  in
  let upgradeAVCBI (vname : string) (aname : string) : unit =
    changeState
      (fun (name, annot) ->
         match annot with
         | AVCBI name' when name = vname && name' = aname ->
             [ (name, AVCB name') ]
         | AZero when name = vname ->
             [ (name, annot); (name, AVCB aname) ]
         | ANonNeg when name = vname ->
             [ (name, annot); (name, AVCB aname) ]
         | _ -> [ (name, annot) ])
      state
  in
  let upgradeAEI (vname : string) : unit =
    changeState
      (fun (name, annot) ->
         match annot with
         | AEI bname when name = vname ->
             [ (name, AE bname); (name, ACC 1) ]
         | _ -> [ (name, annot) ])
      state
  in
  let equalNonZero (e : exp) (sum : summary) : unit =
    match sum with
    | SDerefVar vname ->
        upgradeANT 0 vname
    | SDerefVarOff (bname, oname)
          when FactSet.mem (oname, ANTI (bname, 0)) state.facts ->
        upgradeANTI 0 oname bname
    | SDerefVarOffConst (vname, 1) ->
        upgradeANT 1 vname
    | _ ->
        if !verbose then
          ignore (E.log "unrecognized zero exp: %a == 0\n" d_exp e);
        ()
  in
  let checkLessThan (e1 : exp) (e2 : exp) : unit =
    let s1 = evaluateExp e1 state in
    let s2 = evaluateExp e2 state in
    match s1, s2 with
    | SVar vname, SInt i ->
        let arrays =
          FactSet.fold
            (fun (name, annot) rest ->
               if annot = ACC i then
                 name :: rest
               else
                 rest)
            state.facts
            []
        in
        List.iter (fun aname -> upgradeACCBI vname aname) arrays
    | SVar vname, SVar bname ->
        let arrays =
          FactSet.fold
            (fun (name, annot) rest ->
               if annot = AVC bname then
                 name :: rest
               else
                 rest)
            state.facts
            []
        in
        let arrays2 =
          FactSet.fold
            (fun (name, annot) rest ->
               if annot = AEI bname then
                 name :: rest
               else
                 rest)
            state.facts
            []
        in
        List.iter (fun aname -> upgradeAVCBI vname aname) arrays;
        List.iter (fun aname -> upgradeAEI vname) arrays2
    | SVar vname, _ ->
        let f2 = summaryToFacts s2 state in
        let arrays =
          FactSet.fold
            (fun (name, annot) rest ->
               if annot = AVC "*" then
                 name :: rest
               else
                 rest)
            f2
            []
        in
        List.iter (fun aname -> upgradeAVCBI vname aname) arrays
    | _ -> ()
  in
  let checkEquality (e1 : exp) (e2 : exp) : unit =
    let s1 = evaluateExp e1 state in
    let s2 = evaluateExp e2 state in
    if summaryIsNonZero s2 state then
      equalNonZero e1 s1
  in
  let checkDisequality (e1 : exp) (e2 : exp) : unit =
    let s1 = evaluateExp e1 state in
    let s2 = evaluateExp e2 state in
    if summaryIsZero s2 state then
      equalNonZero e1 s1
  in
  let rec checkCond (cond : exp) (invert : bool) : unit =
    match cond with
    | UnOp (LNot, cond', _) ->
        checkCond cond' (not invert)
    | BinOp ((LAnd | LOr), _, _, _) ->
        E.s (E.bug "&& or || not eliminated by cil\n")
    | BinOp (Lt, cond1, cond2, _) ->
        checkLessThan cond1 cond2
    | BinOp (Eq, cond1, cond2, _) ->
        if invert then
          checkDisequality cond1 cond2
        else
          checkEquality cond1 cond2
    | BinOp (Ne, cond1, cond2, _) ->
        if invert then
          checkEquality cond1 cond2
        else
          checkDisequality cond1 cond2
    | Lval lv ->
        if invert then
          checkEquality cond zero
        else
          checkDisequality cond zero
    | _ ->
        if !verbose then
          ignore (E.log "unrecognized cond: %a\n" d_exp cond);
        ()
  in
  if !verbose then
    ignore (E.log "%a: cond %a\n%a\n" d_loc !currentLoc
                  dn_exp cond d_state state);
  checkCond cond false

let analyzeStmt (stmt : stmt) (state : state) : bool =
  let return = ref true in
  begin
  match stmt.skind with
  | Instr instrs ->
      List.iter
        (fun instr ->
           let doSetNames (vnames : string list) (facts : FactSet.t) : unit =
             let removed =
               FactSet.fold
                 (fun (name, annot) rest ->
                    match annot with
                    | ANTI (vname', _)
                    | AVC vname'
                    | AVCB vname'
                    | AVCBI vname'
                    | ACCB vname'
                    | ACCBI vname' when List.mem vname' vnames -> rest
                    | _ when List.mem name vnames -> rest
                    | _ -> FactSet.add (name, annot) rest)
                 state.facts
                 FactSet.empty
             in
             state.facts <- FactSet.union removed facts;
             (*
             ignore (E.log "%a: %s gets %a\n" d_loc !currentLoc
                           vname d_facts facts)
             *)
           in
           let doSet (lv : lval) (eType : typ) (facts : FactSet.t) : unit =
             let lvType = typeOfLval lv in
             let lvSum = evaluateLval lv state in
             if not (checkBaseTypes lvType eType) then
               ignore (error ("assignment has incompatible types\n" ^^
                              "    to: %a\n  from: %a")
                             d_type lvType d_type eType);
             begin
               match lvSum with
               | SVar vname -> closeVar vname state
               | _ -> ()
             end;
             begin
               match lvSum with
               | SVar vname when varNameIsFS vname ->
                   doSetNames [ vname ] (replaceName "*" vname facts)
               | _ ->
                   (* check base types equal *)
                   let lvFacts = summaryToFacts lvSum state in
                   if not (checkCast lvFacts facts) then
                     ignore (error ("assignment has incompatible facts\n" ^^
                                    "    to: %a\n    from: %a")
                                   d_facts lvFacts d_facts facts)
             end
           in
           if !return then begin
           currentLoc := get_instrLoc instr;
           if !verbose then
             ignore (E.log "%a: instr %a\n%a\n" d_loc !currentLoc
                           dn_instr instr d_state state);
           match instr with
           | Call (None, Lval (Var vi, NoOffset), [ptr; chr; size], l)
                 when vi.vname = "memset" && isZero chr ->
               let t = typeOf ptr in
               let facts, exact = getAllocFact t size state in
               if exact then begin
                 (* TODO: check that all ptrs are nullable *)
                 let ptrSum = evaluateExp ptr state in
                 let ptrFacts = summaryToFacts ptrSum state in
                 if not (checkCast facts ptrFacts) then
                   ignore (error
                           ("argument 1 to memset has incompatible facts\n" ^^
                            "to: %a\n  from: %a\n")
                           d_facts facts d_facts ptrFacts)
               end else
                 ignore (error "cannot verify size of memset")
           | Call (ret, fn, actuals, l) ->
               let fnName =
                 match fn with
                 | Lval (Var vi, NoOffset) -> vi.vname
                 | _ -> "function pointer"
               in
               begin
                 match unrollType (typeOf fn) with
                 | TFun (rtype, argInfo, isVarArg, attrs) as fnType ->
                     let formals = argsToList argInfo in
                     let matches = Hashtbl.create 7 in
                     let removeNames = ref [] in
                     let outSubst = Hashtbl.create 7 in
                     let inOutSubst = Hashtbl.create 7 in
                     let inFacts, outFacts = getFunctionFacts fnType in
                     let rec argIter fn : unit =
                       let rec argIterRec i formals actuals : unit =
                         match formals, actuals with
                         | fcur :: frest, acur :: arest ->
                             fn i fcur acur;
                             argIterRec (i + 1) frest arest
                         | [], [] ->
                             ()
                         | [], _ :: _ ->
                             if isVarArg then begin
                               if not !suppress then
                                 ignore (warning "ignoring vararg args")
                             end else
                               ignore (error "too many actuals")
                         | _ :: _, [] ->
                             ignore (error "too many formals")
                       in
                       argIterRec 1 formals actuals
                     in
                     let rec showWarnings i (fName, fType, _) aExp : unit =
                       let fFacts = typeToFacts "*" fType in
                       if FactSet.is_empty fFacts && isPointerType fType then
                         ignore (warning ("formal parameter %d of " ^^
                                          "%s has no annotations\n")
                                         i fnName)
                     in
                     let rec prepFakeVars i (fname, ftype, _) aExp : unit =
                       let fakeName =
                         if fname <> "" then
                           "@" ^ fname
                         else
                           "@$arg" ^ (string_of_int i)
                       in
                       Hashtbl.add matches fname (SVar fakeName);
                       if isInOutType ftype then begin
                         let aSum = evaluateExp aExp state in
                         match aSum with
                         | SAddrVar vname ->
                             let aFacts = getVarFacts vname state.facts in
                             doSetNames [fakeName] aFacts
                         | _ ->
                             ignore (error ("in/out parameter %d to %s " ^^
                                            "could not be verified\n")
                                     i fnName)
                       end else if not (isOutType ftype) then begin
                         let aSum = evaluateExp aExp state in
                         let aFacts =
                           replaceName "*" fakeName (summaryToFacts aSum state)
                         in
                         doSetNames [fakeName] aFacts
                       end
                     in
                     let rec checkIn i (fname, ftype, _) aExp : unit =
                       let fakeName =
                         if fname <> "" then
                           "@" ^ fname
                         else
                           "@$arg" ^ (string_of_int i)
                       in
                       if not (isIgnoreType ftype) &&
                          not (isOutType ftype) then begin
                         let aFacts = getVarFacts fakeName state.facts in
                         let aType = typeOf aExp in
                         let fFacts = getVarFacts fakeName inFacts in
                         let fType = ftype in
                         if isPointerType fType then
                           addVisited argStats aExp;
                         if not (checkBaseTypes fType aType) then begin
                           ignore (error ("argument %d to %s has " ^^
                                          "incompatible type\n" ^^
                                          "    to: %a\n  from: %a\n")
                                   i fnName d_type fType d_type aType);
                           addFailed argStats aExp;
                         end;
                         if not (checkCast fFacts aFacts) then begin
                           ignore (error ("argument %d to %s has " ^^
                                          "incompatible facts\n" ^^
                                          "    to: %a\n  from: %a\n")
                                   i fnName d_facts fFacts d_facts aFacts);
                           addFailed argStats aExp;
                         end;
                         match evaluateExp aExp state with
                         | SVar name when not (isInOutType ftype) ->
                             Hashtbl.replace inOutSubst fakeName name
                         | SAddrVar name when isInOutType ftype ->
                             Hashtbl.replace inOutSubst fakeName name
                         | _ -> ()
                       end
                     in
                     let rec checkOut i (fname, ftype, _) aExp : unit =
                       let fakeName =
                         if fname <> "" then
                           "@" ^ fname
                         else
                           "@$arg" ^ (string_of_int i)
                       in
                       if isOutType ftype || isInOutType ftype then begin
                         let fFacts = getVarFacts fakeName outFacts in
                         let fType = ftype in
                         match evaluateExp aExp state with
                         | SAddrVar aName ->
                             let aType = varType aName in
                             if not (checkBaseTypes aType fType) then
                               ignore (error ("out parameter %d to %s has " ^^
                                              "incompatible type\n" ^^
                                              "    to: %a\n  from: %a\n")
                                       i fnName d_type aType d_type fType);
                             Hashtbl.add inOutSubst fakeName aName;
                             removeNames := aName :: !removeNames
                         | SInt 0 -> ()
                         | _ ->
                             ignore (error ("out parameter %d to %s " ^^
                                            "could not be verified\n")
                                     i fnName);
                       end
                     in
                     argIter showWarnings;
                     argIter prepFakeVars;
                     argIter checkIn;
                     closeAllVars state;
                     argIter checkOut;
                     let addFacts =
                       Hashtbl.fold replaceName inOutSubst outFacts
                     in
                     doSetNames !removeNames addFacts;
                     begin
                       match ret with
                       | Some lv ->
                           if isAllocator rtype then begin
                             let i = getSizeIndex rtype in
                             let sizeExp = List.nth actuals (i - 1) in
                             let lvType = typeOfLval lv in
                             let facts, _ = getAllocFact lvType sizeExp state in
                             doSet lv lvType facts
                           end else begin
                             let facts = getVarFacts "@$ret" addFacts in
                             doSet lv rtype facts
                           end
                       | None -> ()
                     end;
                     state.facts <-
                       FactSet.diff state.facts
                         (selectFactsEx
                            (fun name -> name.[0] = '@')
                            state.facts);
                     let noReturn =
                       match fn with
                       | Lval (Var vi, NoOffset) ->
                           hasAttribute "noreturn" vi.vattr
                       | _ -> false
                     in
                     if noReturn then
                       return := false
                 | _ ->
                     ignore (error "function has non-function type")
               end
           | Set (lv, e, l) ->
               doSet lv (typeOf e) (summaryToFacts (evaluateExp e state) state)
           | Asm (_, _, _, _, _, l) ->
               if not !suppress then
                 ignore (warning "ignoring asm")
           end)
        instrs
  | Return (eo, l) ->
      if !verbose then
        ignore (E.log "%a: %a\n%a\n" d_loc !currentLoc
                      dn_stmt stmt d_state state);
      begin
        match eo with
        | Some e ->
            let fType =
              match !curFunction.svar.vtype with
              | TFun (rtype, _, _, _) -> rtype
              | t -> E.s (E.bug "expected function type (1): %a\n%a\n"
                                dn_stmt stmt d_type t);
            in
            let eType = typeOf e in
            if not (checkBaseTypes fType eType) then
              ignore (error ("return has incompatible type\n" ^^
                             "    to: %a\n  from: %a")
                            d_type fType d_type eType);
            let fFacts = typeToFacts "*" fType in
            let eFacts = summaryToFacts (evaluateExp e state) state in
            if not (checkCast fFacts eFacts) then
              ignore (error ("return has incompatible facts\n" ^^
                             "    to: %a\n  from: %a")
                            d_facts fFacts d_facts eFacts)
        | None -> ()
      end
  | Loop _
  | Goto _
  | Block _ -> ()
  | If _ -> E.s (E.bug "if statement not handled separately")
  | Break _
  | Switch _
  | Continue _ -> E.s (E.bug "break, switch, or continue not removed")
  | TryFinally _
  | TryExcept _ -> E.s (E.unimp "exceptions")
  end;
  !return

class preFunctionVisitor = object
  inherit nopCilVisitor

  method vlval ((host, offset) : lval) =
    begin
      match host with
      | Var vi -> addVar vi
      | _ -> ()
    end;
    DoChildren
end

let stmtIter (fn : stmt -> unit) (fd : fundec) : unit =
  let stmtline = Hashtbl.create 113 in
  let setLine (stmt : stmt) (line : int) : unit =
    let newLine =
      let locLine = (get_stmtLoc stmt.skind).line in
      if locLine > 0 then
        locLine
      else
        try
          min line (Hashtbl.find stmtline stmt.sid)
        with Not_found ->
          line
    in
    Hashtbl.replace stmtline stmt.sid newLine
  in
  let worklist = Stack.create () in
  let firstStmt = List.hd fd.sbody.bstmts in
  Stack.push firstStmt worklist;
  setLine firstStmt 0;
  while not (Stack.is_empty worklist) do
    let stmt = Stack.pop worklist in
    let line =
      try
        Hashtbl.find stmtline stmt.sid
      with Not_found ->
        E.s (E.bug "expected line number\n")
    in
    List.iter
      (fun succ ->
         if not (Hashtbl.mem stmtline succ.sid) then
           Stack.push succ worklist;
         setLine succ line)
      stmt.succs
  done;
  let getLine stmt =
    try
      Hashtbl.find stmtline stmt.sid
    with Not_found ->
      0
  in
  let sortedStmts =
    List.sort
      (fun s1 s2 -> compare (getLine s1) (getLine s2))
      fd.sallstmts
  in
  List.iter fn sortedStmts

let analyzeFundec (fd : fundec) : unit =
  resetStats expStats;
  resetStats argStats;
  curFunction := fd;
  clearVars ();
  ignore (visitCilFunction (new preFunctionVisitor) fd);
  let stmtState = Hashtbl.create 113 in
  let worklist = Stack.create () in
  let firstStmt = List.hd fd.sbody.bstmts in
  let firstState = makeState fd in
  try
  Hashtbl.add stmtState firstStmt.sid firstState;
  Stack.push firstStmt worklist;
  while not (Stack.is_empty worklist) do
    let stmt = Stack.pop worklist in
    let state =
      try
        Hashtbl.find stmtState stmt.sid
      with Not_found ->
        E.s (E.bug "analyzeAlloc: state not found\n");
    in
    let recordState (newState : state) (succ : stmt) : unit =
      try
        let succState = Hashtbl.find stmtState succ.sid in
        if not (equalStates newState succState) then begin
          Hashtbl.replace stmtState succ.sid
                          (joinStates newState succState);
          Stack.push succ worklist;
        end
      with Not_found ->
        begin
          Hashtbl.replace stmtState succ.sid newState;
          Stack.push succ worklist;
        end
    in
    curStmtId := stmt.sid;
    currentLoc := get_stmtLoc stmt.skind;
    match stmt.skind with
    | If (cond, thenBranch, elseBranch, l) ->
        let getBranchStmt (branch : block) : stmt =
          try
            List.hd branch.bstmts
          with Failure "hd" ->
            dummyStmt
        in
        let thenStmt = getBranchStmt thenBranch in
        let elseStmt = getBranchStmt elseBranch in
        let otherStmts =
          List.filter
            (fun succ -> succ.sid <> thenStmt.sid &&
                         succ.sid <> elseStmt.sid)
            stmt.succs
        in
        let handleStmt (cond : exp) (succ : stmt) : unit =
          let newState = copyState state in
          clearStmtErrors stmt;
          analyzeCond cond newState;
          recordState newState succ;
        in
        begin
          match otherStmts with
          | [] ->
              if thenStmt == dummyStmt || elseStmt == dummyStmt then
                E.s (E.bug "can't handle if statement succs\n");
              handleStmt cond thenStmt;
              handleStmt (UnOp (LNot, cond, intType)) elseStmt;
          | [otherStmt] ->
              if thenStmt != dummyStmt && elseStmt != dummyStmt then
                E.s (E.bug "can't handle if statement succs\n");
              handleStmt cond
                (if thenStmt == dummyStmt then otherStmt else thenStmt);
              handleStmt (UnOp (LNot, cond, intType))
                (if elseStmt == dummyStmt then otherStmt else elseStmt);
          | _ ->
              E.s (E.bug "can't handle if statement succs\n")
        end
    | _ ->
        begin
          let newState = copyState state in
          clearStmtErrors stmt;
          if analyzeStmt stmt newState then
            List.iter (recordState newState) stmt.succs
        end
  done;
  stmtIter showStmtErrors fd;
  clearErrors ();
  tallyStats expStats;
  tallyStats argStats;
  with E.Error ->
    begin
    (*
    let worklist2 = Stack.create () in
    let donelist = Hashtbl.create 113 in
    Stack.push firstStmt worklist2;
    while not (Stack.is_empty worklist2) do
      let stmt = Stack.pop worklist2 in
      let state =
        try
          Hashtbl.find stmtState stmt.sid
        with Not_found ->
          { facts = FactSet.empty; }
      in
      ignore (E.log "%a: %a\n%a\n" d_loc (get_stmtLoc stmt.skind)
                    dn_stmt stmt d_state state);
      Hashtbl.add donelist stmt.sid ();
      let sortedSuccs =
        List.sort
          (fun s2 s1 -> compare (get_stmtLoc s1.skind).line
                                (get_stmtLoc s2.skind).line)
          stmt.succs
      in
      List.iter
        (fun succ ->
           if not (Hashtbl.mem donelist succ.sid) then
             Stack.push succ worklist2)
        sortedSuccs
    done;
    *)
    raise E.Error
    end

class preVisitor = object
  inherit nopCilVisitor

  method vinst (inst : instr) =
    begin
      match inst with
      | Call (ret, fn, args, attrs) ->
          let newArgs =
            match unrollType (typeOf fn) with
            | TFun (_, argInfo, _, _) ->
                let dropCast (t : typ) (e : exp) : exp =
                  match e with
                  | CastE (t', e') when equalTypesNoAttrs t t' -> e'
                  | _ -> e
                in
                let rec matchArgs formals actuals : exp list =
                  match formals, actuals with
                  | (_, fType, _) :: fRest, aExp :: aRest ->
                      (dropCast fType aExp) :: (matchArgs fRest aRest)
                  | [], aRest ->
                      aRest
                  | _, [] ->
                      []
                in
                matchArgs (argsToList argInfo) args
            | t -> E.s (E.bug "expected function type (2): %a\n%a\n"
                              d_instr inst d_type t);
          in
          ChangeDoChildrenPost ([Call (ret, fn, newArgs, attrs)], (fun x -> x))
      | _ ->
          DoChildren
    end

  method vlval ((host, offset) : lval) =
    begin
      match host with
      | Var vi -> addVar vi
      | _ -> ()
    end;
    let rec rewriteIndex (o : offset) (acc : lval) : lval =
      match o with
      | Index (e, o') ->
          let start = StartOf acc in
          let index = BinOp (PlusPI, start, e, typeOf start) in
          let acc' = Mem index, NoOffset in
          rewriteIndex o' acc'
      | Field (fld, o') ->
          let acc' = addOffsetLval (Field (fld, NoOffset)) acc in
          rewriteIndex o' acc'
      | NoOffset -> acc
    in
    ChangeDoChildrenPost (rewriteIndex offset (host, NoOffset), (fun x -> x))
end

class outVisitor = object
  inherit nopCilVisitor

  val mapping : (string, varinfo) Hashtbl.t = Hashtbl.create 5
  val retStmt : stmt ref = ref dummyStmt

  method vfunc (fd : fundec) =
    let instrs = ref [] in
    let retInstrs = ref [] in
    Hashtbl.clear mapping;
    retStmt := dummyStmt;
    List.iter
      (fun vi ->
         if isOutType vi.vtype || isInOutType vi.vtype then begin
           let bt =
             match vi.vtype with
             | TPtr (bt, _) -> bt
             | _ -> E.s (E.bug "expected ptr type\n")
           in
           let vi' = makeLocalVar fd (vi.vname ^ "_local") bt in
           Hashtbl.replace mapping vi.vname vi';
           retInstrs := Set ((Mem (Lval (var vi)), NoOffset), Lval (var vi'),
                             locUnknown) :: !retInstrs;
           if isInOutType vi.vtype then
             instrs := Set (var vi', Lval (Mem (Lval (var vi)), NoOffset),
                            locUnknown) :: !instrs
         end)
      fd.sformals;
    let replace fd =
      fd.sbody <- mkBlock [mkStmt (Instr !instrs); mkStmt (Block fd.sbody)];
      fd
    in
    retStmt := mkStmt (Instr !retInstrs);
    ChangeDoChildrenPost (fd, replace)

  method vstmt (stmt : stmt) =
    match stmt.skind with
    (*
    TODO
    | Return _ when !retStmt != dummyStmt ->
        let replace stmt =
          mkStmt (Block (mkBlock [!retStmt; stmt]))
        in
        ChangeDoChildrenPost (stmt, replace)
    *)
    | _ ->
        DoChildren

  method vinst (inst : instr) =
    match inst with
    | Call (ret, fn, args, attrs) ->
        let newArgs =
          Util.list_map
            (fun arg ->
               match arg with
               | Lval (Var vi, NoOffset) when Hashtbl.mem mapping vi.vname ->
                   AddrOf (var (Hashtbl.find mapping vi.vname))
               | _ -> arg)
            args
        in
        ChangeDoChildrenPost ([Call (ret, fn, newArgs, attrs)], (fun x -> x))
    | _ ->
        DoChildren

  method vlval (lv : lval) =
    match lv with
    | Mem (Lval (Var vi, NoOffset)), NoOffset
          when Hashtbl.mem mapping vi.vname ->
        ChangeDoChildrenPost (var (Hashtbl.find mapping vi.vname),
                              (fun x -> x))
    | _ ->
        DoChildren
end

class ptrArithVisitor = object
  inherit nopCilVisitor

  method vfunc (fd : fundec) =
    prepareCFG fd;
    computeCFGInfo fd false;
    analyzeFundec fd;
    DoChildren
end

let analyzeFile (f : file) : unit =
  ignore (Partial.calls_end_basic_blocks f);
  ignore (Partial.globally_unique_vids f);
  globals := f.globals;
  visitCilFile (new preVisitor) f;
  visitCilFile (new outVisitor) f;
  visitCilFile (new ptrArithVisitor) f;
  verifiedExps := Util.list_map fst expStats.verified;
  verifiedArgs := Util.list_map fst argStats.verified;
  ignore (E.log "\nCCL Results:\n  Derefs: %a\n    Args: %a\n\n"
                d_stats expStats d_stats argStats);
  (*
  ignore (E.log "Verified derefs:\n");
  List.iter
    (fun (e, l) -> ignore (E.log "%a: %a\n" d_loc l d_exp e))
    expStats.verified;
  *)
  if !E.hadErrors then
    E.s (E.error "Verification failed")

let feature : featureDescr = 
  { fd_name = "CCL";
    fd_enabled = ref false;
    fd_description = "CCured Lite";
    fd_extraopt = [
      "--cclverbose", Arg.Set verbose, "Enable verbose output for CCL";
      "--cclsuppress", Arg.Set suppress, "Suppress some CCL warnings";
    ];
    fd_doit = analyzeFile;
    fd_post_check = true;
  } 
