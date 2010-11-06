(* based off of code in CIL, for C to maude *)

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
 
open Cil
open Pretty

open Escape
module E = Errormsg
module H = Hashtbl
module IH = Inthash

let (+^) (d1:Pretty.doc) (d2:string) : Pretty.doc = d1 ++ text d2
let (^+) (d1:string) (d2:Pretty.doc) : Pretty.doc = text d1 ++ d2
let sp : Pretty.doc = (text " ")

let paren (d:Pretty.doc) : Pretty.doc = "(" ^+ d +^ ")"
let giveType (d1:Pretty.doc) (d2:string) : Pretty.doc = paren(d1) ++ (text d2)
let wrap (d1:Pretty.doc) (d2:string) : Pretty.doc = d2 ^+ paren(d1)
let wrapifne (d1:Pretty.doc) (d2:string) = 
	if (d1 = nil) then nil else wrap d1 d2
let parenifne (d1:Pretty.doc) = 
	if (d1 = nil) then nil else paren d1

let typeSig t = 
  typeSigWithAttrs (fun al -> al) t

let replace input output =
    Str.global_replace (Str.regexp_string input) output

let strcontains s1 s2 =
try 
	(Str.search_forward (Str.regexp_string s2) s1 0);
	true
with
| e -> false

let noscores s = 
	(replace "_" "u" s)
	
(* Get the full name of a comp *)
let compFullName comp = 
  (if comp.cstruct then "structDef " else "unionDef ") ^ "(" ^ (noscores comp.cname) ^ ")"
  
let mostNeg32BitInt : int64 = (Int64.of_string "-0x80000000")
let mostNeg64BitInt : int64 = (Int64.of_string "-0x8000000000000000")

let toString d = (sprint 1000 d)

let rec sepRight f sep xs = 
	match xs with
		| x::y::xs -> paren(paren(f x) ++ (text (sep ^ " ")) ++ (sepRight f sep (y::xs)))
		| x::[] -> paren(f x)
		| [] -> nil

(*let rec parenRight f xs = 
	match xs with
		| x::xs -> paren(paren(f x) ++ (parenRight f xs))
		| [] -> nil *)
let rec parenRight f xs = sepRight f " " xs


let d_ikind () = function
    IChar -> text "char"
  | ISChar -> text "signed-char"
  | IUChar -> text "unsigned-char"
  | IBool -> text "_Bool"
  | IInt -> text "int"
  | IUInt -> text "unsigned-int"
  | IShort -> text "short"
  | IUShort -> text "unsigned-short"
  | ILong -> text "long"
  | IULong -> text "unsigned-long"
  | ILongLong -> 
      if !msvcMode then text "__int64" else text "long-long"
  | IULongLong -> 
      if !msvcMode then text "unsigned __int64" 
      else text "unsigned-long-long"
let d_fkind () = function
    FFloat -> text "float"
  | FDouble -> text "double"
  | FLongDouble -> text "long-double"

let d_unop () u =
  match u with
    Neg -> text "-un "
  | BNot -> text "~"
  | LNot -> text "!"	

let d_binop () b =
	match b with
	| PlusA | PlusPI | IndexPI -> text "+"
	(*| PlusPI | IndexPI -> text "+o"*)
	| MinusA | MinusPP | MinusPI -> text "-"
	(*| MinusPP | MinusPI -> text "-o"*)
	| Mult -> text "*"
	| Div -> text "/"
	| Mod -> text "%"
	| Shiftlt -> text "<<"
	| Shiftrt -> text ">>"
	| Lt -> text "<"
	| Gt -> text ">"
	| Le -> text "<="
	| Ge -> text ">="
	| Eq -> text "=="
	| Ne -> text "!="
	| BAnd -> text "&binop"
	| BXor -> text "^"
	| BOr -> text "|"
	| LAnd -> text "&&"
	| LOr -> text "||"
		
	(* constant *)
let d_const () c = 
  match c with
    CInt64(_, _, Some s) -> text s (* Always print the text if there is one *)
  | CInt64(i, ik, None) -> 
      (** We must make sure to capture the type of the constant. For some 
       * constants this is done with a suffix, for others with a cast prefix.*)
      let suffix : string = 
        match ik with
          IUInt -> "@U"
        | ILong -> "@L"
        | IULong -> "@UL"
        | ILongLong -> if !msvcMode then "@L" else "@LL"
        | IULongLong -> if !msvcMode then "@UL" else "@ULL"
        | _ -> ""
      in
      let prefix, cast  = 
        if suffix <> "" then "", false 
        else if ik = IInt then "", false
        else " Cast(" ^ (sprint !lineLength (d_ikind () ik)) ^ ",", true
      in let rest = 
      (* Watch out here for negative integers that we should be printing as 
       * large positive ones *)
      if i < Int64.zero 
          && (match ik with 
            IUInt | IULong | IULongLong | IUChar | IUShort -> true | _ -> false) then
        let high = Int64.shift_right i 32 in
        if ik <> IULongLong && ik <> ILongLong && high = Int64.of_int (-1) then
          (* Print only the low order 32 bits *)
          text (prefix ^ suffix ^ "(" ^"hex(\"" ^ 
                (Int64.format "%x" 
                  (Int64.logand i (Int64.shift_right_logical high 32))
                ^ "\"))"))
        else
          text (prefix ^ suffix ^ "(" ^ "hex(\"" ^ Int64.format "%x" i ^ "\"))")
      else (
        if (i = mostNeg32BitInt) then
          (* sm: quirk here: if you print -2147483648 then this is two tokens *)
          (* in C, and the second one is too large to represent in a signed *)
          (* int.. so we do what's done in limits.h, and print (-2147483467-1); *)
          (* in gcc this avoids a warning, but it might avoid a real problem *)
          (* on another compiler or a 64-bit architecture *)
          (*text (prefix ^ "(-un hex(\"7FFFFFFF\") - 1)")*)
		  text (prefix ^ suffix ^ "(-2147483648)")
        else if (i = mostNeg64BitInt) then
          (* The same is true of the largest 64-bit negative. *)
         (* text (prefix ^ suffix ^ "(-un hex(\"7FFFFFFFFFFFFFFF\") - 1)")*)
		 text (prefix ^ suffix ^ "(-9223372036854775808)")
        else
          text (prefix ^ suffix ^ "(" ^ (Int64.to_string i ^ ")"))
      ) in if cast then rest ++ text ")" else rest

  | CStr(s) -> text ("\"" ^ escape_string s ^ "\"")
  | CWStr(s) -> 
      (* text ("L\"" ^ escape_string s ^ "\"")  *)
      (List.fold_left (fun acc elt -> 
        acc ++ 
        if (elt >= Int64.zero &&
            elt <= (Int64.of_int 255)) then 
          text (escape_char (Char.chr (Int64.to_int elt)))
        else
          ( text (Printf.sprintf "\\x%LX\"" elt) ++ break ++
            (text "\""))
      ) (text "L\"") s ) ++ text "\""
      (* we cannot print L"\xabcd" "feedme" as L"\xabcdfeedme" --
       * the former has 7 wide characters and the later has 3. *)

  (*| CChr(c) -> text ("'" ^ escape_char c ^ "'") *)
  | CChr(c) -> text (string_of_int (int_of_char c))
  (*
  | CReal(_, _, Some s) -> 
	if (strcontains s "f") then (
		text ("@F(" ^ (replace "f" "" s) ^ ")")
	) else if (strcontains s "l") then (
		text ("@L(" ^ (replace "l" "" s) ^ ")")
	) else (text s)
  | CReal(f, fsize, None) -> 
      (match fsize with
         FFloat -> text "@F"
       | FDouble -> nil
       | FLongDouble -> text "@L")
	   ++ paren (text (string_of_float f))*)
  | CReal(f, fsize, _) -> 
      (match fsize with
         FFloat -> text "@F"
       | FDouble -> nil
       | FLongDouble -> text "@L")
	   ++ paren (text (string_of_float f))
  | CEnum(_, s, ei) -> text s
	 
  
(* Helper class for typeSig: replace any types in attributes with typsigs *)
class typeSigVisitor(typeSigConverter: typ->typsig) = object 
  inherit nopCilVisitor 
  method vattrparam ap =
    match ap with
      | ASizeOf t -> ChangeTo (ASizeOfS (typeSigConverter t))
      | AAlignOf t -> ChangeTo (AAlignOfS (typeSigConverter t))
      | _ -> DoChildren
end

let typeSigAddAttrs a0 t = 
  if a0 == [] then t else
  match t with 
    TSBase t -> TSBase (typeAddAttributes a0 t)
  | TSPtr (ts, a) -> TSPtr (ts, addAttributes a0 a)
  | TSArray (ts, l, a) -> TSArray(ts, l, addAttributes a0 a)
  | TSComp (iss, n, a) -> TSComp (iss, n, addAttributes a0 a)
  | TSEnum (n, a) -> TSEnum (n, addAttributes a0 a)
  | TSFun(ts, tsargs, isva, a) -> TSFun(ts, tsargs, isva, addAttributes a0 a)

(* Compute a type signature.
    Use ~ignoreSign:true to convert all signed integer types to unsigned,
    so that signed and unsigned will compare the same. *)
let rec typeSigWithAttrs ?(ignoreSign=false) doattr t = 
  let typeSig = typeSigWithAttrs ~ignoreSign doattr in
  let attrVisitor = new typeSigVisitor typeSig in
  let doattr al = visitCilAttributes attrVisitor (doattr al) in
  match t with 
  | TInt (ik, al) -> 
      let ik' = 
        if ignoreSign then unsignedVersionOf ik  else ik
      in
      TSBase (TInt (ik', doattr al))
  | TFloat (fk, al) -> TSBase (TFloat (fk, doattr al))
  | TVoid al -> TSBase (TVoid (doattr al))
  | TEnum (enum, a) -> TSEnum (enum.ename, doattr a)
  | TPtr (t, a) -> TSPtr (typeSig t, doattr a)
  | TArray (t,l,a) -> (* We do not want fancy expressions in array lengths. 
                       * So constant fold the lengths *)
      let l' = 
        match l with 
          Some l -> begin 
            match constFold true l with 
              Const(CInt64(i, _, _)) -> Some i
            | e -> E.s (E.bug "Invalid length in array type: %a\n" 
                          (fun _ -> E.s (E.bug "pd_exp not initialized")) e)
          end 
        | None -> None
      in 
      TSArray(typeSig t, l', doattr a)

  | TComp (comp, a) -> 
      TSComp (comp.cstruct, comp.cname, doattr (addAttributes comp.cattr a))
  | TFun(rt,args,isva,a) -> 
      TSFun(typeSig rt, 
            List.map (fun (_, atype, _) -> (typeSig atype)) (argsToList args),
            isva, doattr a)
  | TNamed(t, a) -> typeSigAddAttrs (doattr a) (typeSig t.ttype)
  | TBuiltin_va_list al -> TSBase (TBuiltin_va_list (doattr al))     
(* Pretty's api can be found in cil/ocamlutil/pretty.mli *)

class virtual defaultMaudePrinterClass = object (self) 
	inherit defaultCilPrinterClass as super
	
	  val mutable currentFormals : varinfo list = []
  method private getLastNamedArgument (s:string) : exp =
    match List.rev currentFormals with 
      f :: _ -> Lval (var f)
    | [] -> 
        E.s (bug "Cannot find the last named argument when printing call to %s\n" s)

  method private setCurrentFormals (fms : varinfo list) =
    currentFormals <- fms
	
  (*** VARIABLES ***)
  (* variable use *)
  method pVar (v:varinfo) = text v.vname (* ++ (text "/*" ++ v.vdescr ++ text "*/") *)
  
  val mutable currentSwitch : int = 0
  
  (* variable declaration *)
  method pVDecl () (v:varinfo) =
    let stom, rest = separateStorageModifiers v.vattr in
    (* First the storage modifiers *)
	(if (strcontains v.vname "fslAnnotation") then nil else (
     (*(if v.vinline then text "inline " else nil)*)nil
      ++ parenifne(d_storage () v.vstorage)
      ++ (self#pAttrs () stom)
      ++ (self#pType (Some (self#pVar v)) () v.vtype)
      ++ text " "
      ++ self#pAttrs () rest))

  (** Offsets **)
  method pOffset (base: doc) = function
    | NoOffset -> base
    | Field (fi, o) -> 
        self#pOffset (text "_._(" ++ base ++ text ", " ++ text (noscores fi.fname) ++ text ")") o
    | Index (e, o) ->
        self#pOffset (base ++ text "[" ++ self#pExp () e ++ text "]") o

  method pType (nameOpt: doc option) (* Whether we are declaring a name or 
                                      * we are just printing a type *)
               () (t:typ) =       (* use of some type *)	
    let name = match nameOpt with None -> nil | Some d -> d in
	let strname = (sprint 1000 name) in 
    let printAttributes (a: attributes) = 
      let pa = self#pAttrs () a in
      match nameOpt with 
      | None when not !print_CIL_Input && not !msvcMode -> 
          (* Cannot print the attributes in this case because gcc does not 
           * like them here, except if we are printing for CIL, or for MSVC. 
           * In fact, for MSVC we MUST print attributes such as __stdcall *)
          if pa = nil then nil else 
          text "/*" ++ pa ++ text "*/"
      | _ -> pa
    in
	let needsNoComma = (name = nil) || (String.length strname < 1) || (String.rcontains_from strname 0 '[') in
    match t with 
      TVoid a -> text ""
		++ paren (text "void")
		++ if needsNoComma then (nil) else (text ", ")
		++ (self#pAttrs () a)
		++ text " " 
		++ name

    | TInt (ikind,a) -> text ""
		++ paren (d_ikind () ikind)
		++ (if needsNoComma then (nil) else (text ", "))
		(* ++ if (name = nil) then (nil) else (text " xx " ++ name ++ text " xx, ") *)
		(*if (name = nil) then (nil) else (
			match name with 
			(* text ", " *)
		)*)
		++ (self#pAttrs () a)
		++ text " "
		(* ++ if (name = nil) then (nil) else (text " x") *)
		++ name
		(* ++ if (name = nil) then (nil) else (text "x")*)

    | TFloat(fkind, a) -> 
        d_fkind () fkind 
		++ (if needsNoComma then (nil) else (text ", "))
          ++ self#pAttrs () a 
          ++ text " " 
          ++ name

    | TComp (comp, a) -> (* A reference to a struct *)
        let su = if comp.cstruct then "struct" else "union" in
          text (su ^ " ")
		  ++  (text ("(" ^ (noscores comp.cname) ^ ") " )
          ++ self#pAttrs () a 
		  ++ (if needsNoComma then (nil) else (text ", "))
          ++ name)
          
    | TEnum (enum, a) -> 
        text ("(enum(" ^ (noscores enum.ename) ^ ")) ")
          ++ self#pAttrs () a 
		  ++ (if needsNoComma then (nil) else (text ", "))
          ++ name
    | TPtr (bt, a)  -> 
        (* Parenthesize the ( * attr name) if a pointer to a function or an 
         * array. However, on MSVC the __stdcall modifier must appear right 
         * before the pointer constructor "(__stdcall *f)". We push them into 
         * the parenthesis. *)
        let (paren: doc option), (bt': typ) = 
          match bt with 
            TFun(rt, args, isva, fa) when !msvcMode -> 
              let an, af', at = partitionAttributes ~default:AttrType fa in
              (* We take the af' and we put them into the parentheses *)
              Some (text "(" ++ printAttributes af'), 
              TFun(rt, args, isva, addAttributes an at)

          | TFun _ | TArray _ -> Some (text "("), bt

          | _ -> None, bt
        in
        let name' = text "Pointer(" ++ printAttributes a ++ name ++ text ")" in
        let name'' = (* Put the parenthesis *)
          match paren with 
            Some p -> p ++ name' ++ text ")" 
          | _ -> name' 
        in
		if (name = nil) then (
			text "Pointer(" ++ self#pType None () bt' ++ text ")"
		) else (
			self#pType 
			(Some name'')
			() 
			bt'
		)
		
    | TArray (elemt, lo, a) -> 
        (* ignore the const attribute for arrays *)
        let a' = dropAttributes [ "const" ] a in 
        let name' = 
          if a' == [] then name else
          if nameOpt == None then printAttributes a' else 
          text "(" ++ printAttributes a' ++ name ++ text ")" 
        in
		self#pType
          (Some (name'
                   ++ text "["
                   ++ (match lo with None -> nil | Some e -> self#pExp () e)
                   ++ text "]"))
          ()
          elemt
		  
		(*let subt = (self#pType None () elemt) in
			subt ++ (((if (name' = nil) then (nil) else (text ", ") ++ name')
			   ++ text "[" 
			   ++ (match lo with None -> nil | Some e -> self#pExp () e)
			   ++ text "]"))*)
(*
    | TArray (elemt, lo, a) -> 
        (* ignore the const attribute for arrays *)
        let a' = dropAttributes [ "const" ] a in 
        let name' = 
          if a' == [] then name else
          if nameOpt == None then printAttributes a' else 
          text "(" ++ printAttributes a' ++ name ++ text ")" 
        in
       (self#pType 
          None
          ()
          elemt) ++ ((
			if (name' = nil) then (nil) else (text ", ") ++ name'
                   ++ text "[" 
                   ++ (match lo with None -> nil | Some e -> self#pExp () e)
                   ++ text "]"))
 *)         
    | TFun (restyp, args, isvararg, a) -> 
        let name' = 
          if a == [] then (name ++ if name = nil then nil else text ", ") else 
          if nameOpt == None then printAttributes a else
          text "(" ++ printAttributes a ++ name ++ text "), " 
        in
        self#pType 
          (Some
             (wrap (name'
                ++ text " Parameter-Type-List("
                ++ (
                      (if args = Some [] && isvararg then 
                        text "..."
                      else
                        (if args = None then nil 
                        (* else if args = Some [] then text "void" *)
						else if args = Some [] then wrap (self#pType (None) () (TVoid [])) "Parameter-Declaration"
                        else 
                          let pArg (aname, atype, aattr) = 
                            let stom, rest = separateStorageModifiers aattr in
                            (* First the storage modifiers *)
							  wrap (
							  let optionName = 
									if aname = "" then None else Some (text aname) in
                              (self#pAttrs () stom)
                              ++ (self#pType optionName () atype)
                              ++ text " "
                              ++ self#pAttrs () rest
								) "Parameter-Declaration"
                          in
                          (docList ~sep:(text " ,., " ++ break) pArg) () 
                            (argsToList args))
                          ++ (if isvararg then break ++ text ",., ..." else nil))
                      )
                ++ text ")") "Direct-Function-Declarator"))
          ()
          restyp

  | TNamed (t, a) ->
      text t.tname 
	  ++ if (name = nil) then (nil) else (text ", ")
	  ++ self#pAttrs () a ++ text " " ++ name

  | TBuiltin_va_list a -> 
      text "__builtin_va_list"
       ++ self#pAttrs () a 
        ++ text " " 
        ++ name
	
	
	(***************************************************)
	
	(*** INSTRUCTIONS ****)
  method pInstr () (i:instr) =       (* imperative instruction *)
    match i with
    | Set(lv,e,l) -> begin
        (* Be nice to some special cases *)
        (match e with
          BinOp((PlusA|PlusPI|IndexPI),Lval(lv'),Const(CInt64(one,_,_)),_)
            when Util.equals lv lv' && one = Int64.one && not !printCilAsIs ->
              self#pLineDirective l
                ++ self#pLval () lv
                ++ text (" ++ " ^ self#getPrintInstrTerminator ())

        | BinOp((MinusA|MinusPI),Lval(lv'),
                Const(CInt64(one,_,_)), _) 
            when Util.equals lv lv' && one = Int64.one && not !printCilAsIs ->
                  self#pLineDirective l
                    ++ self#pLval () lv
                    ++ text (" -- " ^ self#getPrintInstrTerminator ()) 

        | BinOp((PlusA|PlusPI|IndexPI),Lval(lv'),Const(CInt64(mone,_,_)),_)
            when Util.equals lv lv' && mone = Int64.minus_one 
                && not !printCilAsIs ->
              self#pLineDirective l
                ++ self#pLval () lv
                ++ text (" -- " ^ self#getPrintInstrTerminator ())

        | BinOp((PlusA|PlusPI|IndexPI|MinusA|MinusPP|MinusPI|BAnd|BOr|BXor|
          Mult|Div|Mod|Shiftlt|Shiftrt) as bop,
                Lval(lv'),e,_) when Util.equals lv lv' 
                && not !printCilAsIs ->
                  self#pLineDirective l
                    ++ self#pLval () lv
                    ++ text " " ++ d_binop () bop
                    ++ text "= "
                    ++ self#pExp () e
                    ++ text (self#getPrintInstrTerminator ())
                    
        | _ ->
			let f = (self#pLineDirective l
	              ++ self#pLval () lv
	              ++ text " := "
	              ++ self#pExp () e
	              ++ text (self#getPrintInstrTerminator ())) in
			let myv = (match lv with
			| (Var fslv, _) -> Some fslv.vname
			| (Mem _, _) -> None ) in
			match myv with
			| Some name -> 
				if strcontains name "fslAnnotation" then 
					match e with
					| CastE(t,Const(CStr(s))) -> 
				          (text "/* "
							++ text s
							(* ++ self#pExp () e*)
							++ text " */" )
				else f
			| None -> f
	            
        )   
    end
      (* In cabs2cil we have turned the call to builtin_va_arg into a 
       * three-argument call: the last argument is the address of the 
       * destination *)
    | Call(None, Lval(Var vi, NoOffset), [dest; SizeOf t; adest], l) 
        when vi.vname = "__builtin_va_arg" && not !printCilAsIs -> 
          let destlv = match stripCasts adest with 
            AddrOf destlv -> destlv
              (* If this fails, it's likely that an extension interfered
                 with the AddrOf *)
          | _ -> E.s (E.bug 
                        "%a: Encountered unexpected call to %s with dest %a\n" 
                        d_loc l vi.vname self#pExp adest)
          in
          self#pLineDirective l
	    ++ self#pLval () destlv ++ text " = "
                   
            (* Now the function name *)
            ++ text "__builtin_va_arg"
            ++ text "(" ++ (
                              (* Now the arguments *)
                              self#pExp () dest 
                              ++ chr ',' ++ break 
                              ++ self#pType None () t
                              )
            ++ text (")" ^ (self#getPrintInstrTerminator ()))

      (* In cabs2cil we have dropped the last argument in the call to 
       * __builtin_va_start and __builtin_stdarg_start. *)
    | Call(None, Lval(Var vi, NoOffset), [marker], l) 
        when ((vi.vname = "__builtin_stdarg_start" ||
               vi.vname = "__builtin_va_start") && not !printCilAsIs) -> 
        if currentFormals <> [] then begin
		(*if (super#getLastNamedArgument ""; true) then begin*)
          let last = self#getLastNamedArgument vi.vname in
          self#pInstr () (Call(None,Lval(Var vi,NoOffset),[marker; last],l))
        end
        else begin
          (* We can't print this call because someone called pInstr outside 
             of a pFunDecl, so we don't know what the formals of the current
             function are.  Just put in a placeholder for now; this isn't 
             valid C. *)
          self#pLineDirective l
          ++ dprintf 
            "%s(%a, /* last named argument of the function calling %s */)"
            vi.vname self#pExp marker vi.vname
          ++ text (self#getPrintInstrTerminator())
        end
      (* In cabs2cil we have dropped the last argument in the call to 
       * __builtin_next_arg. *)
    | Call(res, Lval(Var vi, NoOffset), [ ], l) 
        when vi.vname = "__builtin_next_arg" && not !printCilAsIs -> begin
          let last = self#getLastNamedArgument vi.vname in
          self#pInstr () (Call(res,Lval(Var vi,NoOffset),[last],l))
        end

      (* In cparser we have turned the call to 
       * __builtin_types_compatible_p(t1, t2) into 
       * __builtin_types_compatible_p(sizeof t1, sizeof t2), so that we can
       * represent the types as expressions. 
       * Remove the sizeofs when printing. *)
    | Call(dest, Lval(Var vi, NoOffset), [SizeOf t1; SizeOf t2], l) 
        when vi.vname = "__builtin_types_compatible_p" && not !printCilAsIs -> 
        self#pLineDirective l
          (* Print the destination *)
        ++ (match dest with
              None -> nil
            | Some lv -> self#pLval () lv ++ text " = ")
          (* Now the call itself *)
        ++ dprintf "%s(%a, %a)" vi.vname
             (self#pType None) t1  (self#pType None) t2
        ++ text (self#getPrintInstrTerminator())
    | Call(_, Lval(Var vi, NoOffset), _, l) 
        when vi.vname = "__builtin_types_compatible_p" && not !printCilAsIs -> 
        E.s (bug "__builtin_types_compatible_p: cabs2cil should have added sizeof to the arguments.")
    | Call(dest,e,args,l) ->
        self#pLineDirective l
          ++ (match dest with
            None -> nil
          | Some lv -> 
              self#pLval () lv ++ text " := ")
			++  
			let maybeCast = (
				match dest with
				None -> nil
				| Some lv -> 
                (* Maybe we need to print a cast *)
                (let destt = typeOfLval lv in
                match unrollType (typeOf e) with
                  TFun (rt, _, _, _) 
                      when not (Util.equals (typeSig rt)
                                            (typeSig destt)) ->
                    text "(" ++ self#pType None () destt ++ text ")"
                | _ -> nil)) in
          (* Now the function name *)
		  let pref = 
		  (text "Apply(" ++ 
			(let ed = self#pExp () e in
              match e with 
                Lval(Var fslv, _) -> ed
              | _ -> text "(" ++ ed ++ text ")")
          ++ text ", (" ++ 
          (
             (* Now the arguments *)
			 
             if (List.length args = 0) then text ".List{Expression}" else (docList ~sep:(text " .,. " ++ break) (self#pExp ()) () args)
             )
		++ text ")"
        ++ text (")"))
		in let f = 
			((if (maybeCast != nil) then ((text "Cast(") ++ maybeCast ++ (text ", ") ++ pref ++ (text ")")) else pref) ++ text (self#getPrintInstrTerminator ()) )
		in
		  let myv = (
			match e with 
                Lval(Var fslv, _) -> Some fslv.vname
              | _ -> None
			 ) in 
			match myv with
				| Some name -> 
					if strcontains name "fslAnnotation" then 
						let rec newe () e = (
							match e with
							| CastE(t,e') -> (newe () e')
							| Const(CStr(s)) -> s
							| Lval(Var vi, o) -> vi.vname
						) in
						let (s, m) = (
							match args with
							| x::xs -> ((newe () x), xs)
							(*(docList ~sep:(text ";;" ++ break) (newe ()) () args)*) 
						) in let rec f (s, m) = (
							match m with
							| (pattern :: replacement :: ms) -> 
								let var1 = noscores (newe () pattern) in
								let var2 = noscores (newe () replacement) in
								f (((replace var1 var2) s), ms)
							| [] -> text ("(annotation(" ^ s ^ ") ;) ")
						) in f (s, m)
					else f
				| None -> f
        
    | _ -> super#pInstr () i

	
  (* The pBlock will put the unalign itself *)
  method pBlock () (blk: block) = 
    (*let rec dofirst () = function
        [] -> nil
      | [x] -> paren(self#pStmtNext invalidStmt () x)
      | x :: rest -> paren(dorest nil x rest)
    and dorest acc prev = function
        [] -> paren(acc ++ paren(self#pStmtNext invalidStmt () prev))
      | x :: rest -> 
          paren(dorest (acc ++ paren(self#pStmtNext x () prev) ++ line)
            x rest)
    in*)
    (* Let the host of the block decide on the alignment. The d_block will 
     * pop the alignment as well  *)
		(if blk.battrs <> [] then 
			self#pAttrsGen true blk.battrs
		else nil)
		++ (parenRight (fun x -> self#pStmtNext x () x) blk.bstmts )
		++ line

  method private pAttrsGen (block: bool) (a: attributes) = 
	text " "
	  
  method private pStmtNext (next: stmt) () (s: stmt) =
    (* print the labels *)
    ((docList ~sep:line (fun l -> self#pLabel () l)) () s.labels)
	(*(parenRight (self#pLabel ()) s.labels)*)
      (* print the statement itself. If the labels are non-empty and the
      * statement is empty, print a semicolon  *)
      ++ 
      paren(if s.skind = Instr [] && s.labels <> [] then
        text "EmptyStatement ;"
      else
        (if s.labels <> [] then line else nil) 
          ++ paren(self#pStmtKind next () s.skind))
		  
	method private pLabel () = function
      Label (s, _, true) -> text (noscores s ^ " : ")
    | Label (s, _, false) -> text (noscores s ^ " : ") (*  CIL Label  *)
    | Case (e, _) -> text ("case(" ^ string_of_int currentSwitch ^ ") ") ++ self#pExp () e ++ text " : "
    | Default _ -> text ("default(" ^ string_of_int currentSwitch ^ ") : ")
	
(*** L-VALUES ***)
  method pLval () (lv:lval) =  (* lval (base is 1st field)  *)
    match lv with
      Var vi, o -> self#pOffset (self#pVar vi) o
    | Mem e, Field(fi, o) ->
        self#pOffset
          (((self#pExp () e)) ++ text (" -> " ^ (noscores fi.fname))) o
    | Mem e, NoOffset -> 
		wrap (self#pExp () e) "Deref"
    | Mem e, o ->
        self#pOffset
          (text "Deref(" ++ self#pExp () e ++ text ")") o

  method private pFunDecl () f =
      paren(self#pVDecl () f.svar
      ++  line
      ++ text "{ "
      ++ (
            (* locals. *)
            (* ++ (docList ~sep:line (fun vi -> self#pVDecl () vi ++ text ";") *)
			(*(docList ~sep:line (fun vi -> self#pVDecl () vi) () f.slocals)*)
				(parenRight (fun x -> (wrap (self#pVDecl () x) "Local")) f.slocals)
            ++ line ++ line
            (* the body *)
            ++ ((* remember the declaration *) currentFormals <- f.sformals; 
                let body = self#pBlock () f.sbody in
                currentFormals <- [];
                body))
      ++ line
      ++ text "}")

  (*** GLOBALS ***)
  method pGlobal () (g:global) : doc =       (* global (vars, types, etc.) *)
    match g with 
    | GFun (fundec, l) ->
        (* If the function has attributes then print a prototype because 
        * GCC cannot accept function attributes in a definition *)
        let oldattr = fundec.svar.vattr in
        (* Always pring the file name before function declarations *)
        let proto = 
          if oldattr <> [] then 
            (self#pLineDirective l) ++ (self#pVDecl () fundec.svar) 
               ++ line 
          else nil in
        (* Temporarily remove the function attributes *)
        fundec.svar.vattr <- [];
        let body = (self#pLineDirective ~forcefile:true l) 
                      ++ (self#pFunDecl () fundec) in
        fundec.svar.vattr <- oldattr;
        proto ++ body ++ line
          
    | GType (typ, l) ->
		typ.tname <- "typedefName(" ^ typ.tname ^ ")";
        self#pLineDirective ~forcefile:true l ++
          text "(Typedef ("
          ++ (self#pType (Some (text (typ.tname))) () typ.ttype)
          ++ text ")) \n"

    | GEnumTag (enum, l) ->
        self#pLineDirective l ++
          text "enum(" ++ text (" " ^ (noscores enum.ename)) ++
          text ", " ++ line
          ++ (docList ~sep:(text ".,." ++ line)
                (fun (n,i, loc) -> 
                  paren (text ((noscores n) ^ " := ") 
                    ++ self#pExp () i))
                () enum.eitems)
          ++ line ++ text ") " 
          ++ self#pAttrs () enum.eattr ++ text"\n"

    | GEnumTagDecl (enum, l) -> (* This is a declaration of a tag *)
        self#pLineDirective l ++
          text ("enum(" ^ (noscores enum.ename) ^ ")\n")

    | GCompTag (comp, l) -> (* This is a definition of a tag *)
        let n = noscores comp.cname in
        let su, su1, su2 =
          if comp.cstruct then "structDef", "str", "uctDef"
          else "unionDef",  "uni", "onDef"
        in
        let sto_mod, rest_attr = separateStorageModifiers comp.cattr in
        self#pLineDirective ~forcefile:true l ++
          text su1 ++ (text su2 ++ paren ((self#pAttrs () sto_mod)
                         ++ text n ++ text ", "
                         ++ text " (" ++ line
                         ++ (*((docList ~sep:line ((self#pFieldDecl ()) )) () comp.cfields)*)
							(*(parenRight (self#pFieldDecl ()) comp.cfields)*)
							(sepRight (self#pFieldDecl ()) ",.," comp.cfields)
						 )
                         )
          ++ line ++ text ")" ++
          (self#pAttrs () rest_attr) ++ text "\n"

    | GCompTagDecl (comp, l) -> (* This is a declaration of a tag *)
        self#pLineDirective l ++
          text (compFullName comp) ++ text "\n"

    | GVar (vi, io, l) ->
        self#pLineDirective ~forcefile:true l ++
          self#pVDecl () vi
          ++ chr ' '
          ++ (match io.init with
            None -> nil
          | Some i -> text " = " ++ 
                (let islong = 
                  match i with
                    CompoundInit (_, il) when List.length il >= 8 -> true
                  | _ -> false 
                in
                if islong then 
                  line ++ self#pLineDirective l ++ text "  " 
                else nil) ++
                (self#pInit () i))
          ++ text "\n"
      
    (* print global variable 'extern' declarations, and function prototypes *)    
    | GVarDecl (vi, l) ->
        if not !printCilAsIs && H.mem builtinFunctions vi.vname then begin
          (* Compiler builtins need no prototypes. Just print them in
             comments. *)
          text "/* compiler builtin: \n   " ++
            (self#pVDecl () vi)
            ++ text ";  */\n"
          
        end else
          self#pLineDirective l ++
            (self#pVDecl () vi)
            ++ text "\n"

    | GAsm (s, l) ->
        self#pLineDirective l ++
          text ("__asm__(\"" ^ escape_string s ^ "\");\n")

    | GPragma (Attr(an, args), l) ->
        (* sm: suppress printing pragmas that gcc does not understand *)
        (* assume anything starting with "ccured" is ours *)
        (* also don't print the 'combiner' pragma *)
        (* nor 'cilnoremove' *)
        let suppress =
          not !print_CIL_Input && 
          not !msvcMode &&
          ((startsWith "box" an) ||
           (startsWith "ccured" an) ||
           (an = "merger") ||
           (an = "cilnoremove")) in
        let d =
	  match an, args with
	  | _, [] ->
              text an
	  | "weak", [ACons (symbol, [])] ->
	      text "weak " ++ text symbol
	  | _ ->
            text (an ^ "(")
              ++ docList ~sep:(chr ',') (self#pAttrParam ()) () args
              ++ text ")"
        in
        self#pLineDirective l 
          ++ (if suppress then text "/* " else text "")
          ++ (text "#pragma ")
          ++ d
          ++ (if suppress then text " */\n" else text "\n")

    | GText s  -> 
        if s <> "//" then 
          text s ++ text "\n"
        else
          nil


   method dGlobal (out: out_channel) (g: global) : unit = 
     (* For all except functions and variable with initializers, use the 
      * pGlobal *)
     match g with 
       GFun (fdec, l) -> 
         (* If the function has attributes then print a prototype because 
          * GCC cannot accept function attributes in a definition *)
         let oldattr = fdec.svar.vattr in
         fprint out !lineLength
           ((self#pLineDirective ~forcefile:true l));
         (* Temporarily remove the function attributes *)
         fdec.svar.vattr <- [];
         fprint out !lineLength (self#pFunDecl () fdec);               
         fdec.svar.vattr <- oldattr;
         output_string out "\n"

     | GVar (vi, {init = Some i}, l) -> begin
         fprint out !lineLength 
			
           (text "(" ++ self#pLineDirective ~forcefile:true l ++
              self#pVDecl () vi
              ++ text " = " 
              ++ (let islong = 
                match i with
                  CompoundInit (_, il) when List.length il >= 8 -> true
                | _ -> false 
              in
              if islong then 
                line ++ self#pLineDirective l ++ text "  " 
              else nil)); 
         self#dInit out 3 i;
         output_string out ")\n"
     end

     | g -> fprint out !lineLength (self#pGlobal () g)	  


	 
	  (*** EXPRESSIONS ***)
  method pExp () (e: exp) : doc = 
    paren(
    match e with
      Const(c) -> (d_const () c)
    | Lval(l) -> self#pLval () l
    | UnOp(u,e1,_) -> 
        (d_unop () u) ++ chr ' ' ++ (self#pExp () e1)
          
    | BinOp(b,e1,e2,_) -> 
        (self#pExp () e1)
          ++ chr ' ' 
          ++ (d_binop () b)
          ++ chr ' '
          ++ (self#pExp () e2)
          

    | CastE(t,e) -> 
        text "Cast((" 
          ++ self#pType None () t
          ++ text "),("
          ++ self#pExp () e
		  ++ text "))"

    | SizeOf (t) -> 
        text "sizeof(" ++ self#pType None () t ++ chr ')'
    | SizeOfE (Lval (Var fv, NoOffset)) when fv.vname = "__builtin_va_arg_pack" && (not !printCilAsIs) -> 
        text "__builtin_va_arg_pack()"
    | SizeOfE (e) ->  
        text "sizeof(" ++ self#pExp () e ++ chr ')'

    | SizeOfStr s -> 
        text "sizeof(" ++ d_const () (CStr s) ++ chr ')'

    | AlignOf (t) -> 
        text "__alignof__(" ++ self#pType None () t ++ chr ')'
    | AlignOfE (e) -> 
        text "__alignof__(" ++ self#pExp () e ++ chr ')'
    | AddrOf(lv) -> 
        text "& " ++ (self#pLval () lv)
          
    | StartOf(lv) -> self#pLval () lv
	)
	 
	method private pStmtKind (next: stmt) () = function
      Return(None, l) ->
        self#pLineDirective l
          ++ text "return ;"

    | Return(Some e, l) ->
        self#pLineDirective l
          ++ text "return ("
          ++ self#pExp () e
          ++ text ");"
          
    | Goto (sref, l) -> begin
        (* Grab one of the labels *)
        let rec pickLabel = function
            [] -> None
          | Label (l, _, _) :: _ -> Some l
          | _ :: rest -> pickLabel rest
        in
        match pickLabel !sref.labels with
          Some l -> text ("goto " ^ (noscores l) ^ " ;")
        | None -> 
            ignore (error "Cannot find label for target of goto");
            text "goto __invalid_label ;"
		end 
	
    | Break l ->
        self#pLineDirective l
          ++ text "break ;"

    | Continue l -> 
        self#pLineDirective l
          ++ text "continue ;"

    | Instr il ->
          (* (docList ~sep:line (fun i -> paren(self#pInstr () i)) () il) *)
			(parenRight (self#pInstr ()) il)

    | If(be,t,{bstmts=[];battrs=[]},l) when not !printCilAsIs ->
        self#pLineDirective l
          ++ text "if"
          ++ (text " ("
                ++ self#pExp () be
                ++ text ") "
                ++ self#pBlock () t)
          
    | If(be,t,{bstmts=[{skind=Goto(gref,_);labels=[]}];
                battrs=[]},l)
     when !gref == next && not !printCilAsIs ->
       self#pLineDirective l
         ++ text "if"
         ++ (text " ("
               ++ self#pExp () be
               ++ text ") "
               ++ self#pBlock () t)

    | If(be,{bstmts=[];battrs=[]},e,l) when not !printCilAsIs ->
        self#pLineDirective l
          ++ text "if"
          ++ (text " ("
                ++ self#pExp () (UnOp(LNot,be,intType))
                ++ text ") "
                ++ self#pBlock () e)

    | If(be,{bstmts=[{skind=Goto(gref,_);labels=[]}];
           battrs=[]},e,l)
      when !gref == next && not !printCilAsIs ->
        self#pLineDirective l
          ++ text "if"
          ++ (text " ("
                ++ self#pExp () (UnOp(LNot,be,intType))
                ++ text ") "
                ++ self#pBlock () e)
          
    | If(be,t,e,l) ->
        self#pLineDirective l
          ++ (text "if"
                ++ (text " ("
                      ++ self#pExp () be
                      ++ text ") "
                      ++ self#pBlock () t)
                ++ text " "   (* sm: indent next code 2 spaces (was 4) *)
                ++ (text "else "
                      ++ self#pBlock () e)
          )
          
    | Switch(e,b,_,l) -> currentSwitch <- currentSwitch + 1;
        self#pLineDirective l
          ++ (text ("switch(" ^ string_of_int currentSwitch ^ ") (")
                ++ self#pExp () e
                ++ text ") "
                ++ self#pBlock () b)
    | Loop(b, l, _, _) -> begin
        (* Maybe the first thing is a conditional. Turn it into a WHILE *)
        try
          let term, bodystmts =
            let rec skipEmpty = function
                [] -> []
              | {skind=Instr [];labels=[]} :: rest -> skipEmpty rest
              | x -> x
            in
            (* Bill McCloskey: Do not remove the If if it has labels *)
            match skipEmpty b.bstmts with
              {skind=If(e,tb,fb,_); labels=[]} :: rest 
                                              when not !printCilAsIs -> begin
                match skipEmpty tb.bstmts, skipEmpty fb.bstmts with
                  [], {skind=Break _; labels=[]} :: _  -> e, rest
                | {skind=Break _; labels=[]} :: _, [] 
                                     -> UnOp(LNot, e, intType), rest
                | _ -> raise Not_found
              end
            | _ -> raise Not_found
          in
          self#pLineDirective l
            ++ text "wh"
            ++ (text "ile ("
                  ++ self#pExp () term
                  ++ text ") "
                  ++ self#pBlock () {bstmts=bodystmts; battrs=b.battrs})

        with Not_found ->
          self#pLineDirective l
            ++ text "wh"
            ++ (text "ile (1) "
                  ++ self#pBlock () b)
    end
    | Block b -> self#pBlock () b
	| _ -> E.s (E.bug "Not handling this stmtkind")

	method pFieldDecl () fi = 
	 match fi.fbitfield with 
	 | None -> ((self#pType
        (Some (text (if fi.fname = missingFieldName then "" else (fi.fname))))
        () 
        fi.ftype)
	       ++ text " "
	       ++ self#pAttrs () fi.fattr) 
     | Some i -> ( (self#pType
        (Some (text (if fi.fname = missingFieldName then ("BitField(" ^ string_of_int i ^ ")") else ("BitField(" ^ fi.fname ^ ", " ^ string_of_int i ^ ")"))))
        () 
        fi.ftype)
       ++ text " "
       ++ self#pAttrs () fi.fattr)
	   (*text ", " ++ num i ++ text " ")*)
	   
  method pInit () =	
	(*(print_string ("asdf");*)
  function 
      SingleInit e -> wrap (self#pExp () e) "InitItem"
    | CompoundInit (t, initl) -> 
      (* We do not print the type of the Compound *)
        let d_oneInit = function
            Field(f, NoOffset), i -> 
              text ("Designation(FieldDesignator(" ^ (noscores f.fname) ^ "), ") 
              ++ self#pInit () i
			  ++ text ")"
          | Index(e, NoOffset), i -> 
                (text "Designation(ArrayDesignator(" ++ self#pExp () e ++ text "), ") ++ 
                self#pInit () i
				++ text ")"
          | _ -> E.s (unimp "Trying to print malformed initializer")
        in
        text "InitList(" ++ (((docList ~sep:(text ".,." ++ break) d_oneInit) () initl) 
                     )
          ++ chr ')'
		(*function SingleInit e -> self#pExp () e
    | CompoundInit (t, initl) -> 
         let printDesignator = 
          if not !msvcMode then begin
            (* Print only for union when we do not initialize the first field *)
            match unrollType t, initl with
              TComp(ci, _), [(Field(f, NoOffset), _)] -> 
                if not (ci.cstruct) && ci.cfields != [] && 
                  (List.hd ci.cfields) != f then
                  true
                else
                  false
            | _ -> false
          end else 
            false 
        in
        let d_oneInit = function
            Field(f, NoOffset), i -> 
              (if printDesignator then 
                text ("." ^ f.fname ^ " = ") 
              else nil) ++ self#pInit () i
          | Index(e, NoOffset), i -> 
              (if printDesignator then 
                text "[" ++ self#pExp () e ++ text "] = " else nil) ++ 
                self#pInit () i
          | _ -> E.s (unimp "Trying to print malformed initializer")
        in
        chr '{' ++ (((docList ~sep:(text " .,. " ++ break) d_oneInit) () initl) 
                      )
          ++ chr '}'*)
		  
 (* dump initializers to a file. *)
  method dInit (out: out_channel) (ind: int) (i: init) = 
    (* Dump an array *)
    let dumpArray (bt: typ) (il: 'a list) (getelem: 'a -> init) = 
      let onALine = (* How many elements on a line *)
        match unrollType bt with TComp _ | TArray _ -> 1 | _ -> 4
      in
      let rec outputElements (isfirst: bool) (room_on_line: int) = function
          [] -> output_string out "}"
        | (i: 'a) :: rest -> 
            if not isfirst then output_string out ".,. ";
            let new_room_on_line = 
              if room_on_line == 0 then begin 
                output_string out "\n"; output_string out (String.make ind ' ');
                onALine - 1
              end else 
                room_on_line - 1
            in
            self#dInit out (ind + 2) (getelem i);
            outputElements false new_room_on_line rest
      in
      output_string out "{ ";
      outputElements true onALine il
    in
    match i with 
      SingleInit e -> 
        fprint out !lineLength (indent ind (self#pExp () e))
    | CompoundInit (t, initl) -> begin 
        match unrollType t with 
          TArray(bt, _, _) -> 
            dumpArray bt initl (fun (_, i) -> i)
        | _ -> 
            (* Now a structure or a union *)
            fprint out !lineLength (indent ind (self#pInit () i))
    end


			  
end (* class defaultCilPrinterClass *)
