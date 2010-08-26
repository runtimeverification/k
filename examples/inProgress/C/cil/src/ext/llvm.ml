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

(* Generate LLVM code for a CIL file. This provides an alternate code generation
   path from CIL (vs the usual "regenerate and compile C code"), which gives more
   code generation flexibility (to the extent that LLVM is more flexible than C).

   The current implementation is targeted to x86 processors using gcc's C dialect.
   Supporting MSVC or other processors shouldn't require too much work - x86
   and gcc dependencies are marked with comments starting with X86: and GCC:
   respectively. We handle all of C, except:

     bitfields, shows up in:
     - field read/writes
     - structure declarations
     inline and module-level assembly

     gcc inline assembly

     gcc pragmas/attributes (those not handled by CIL directly)

     "align" directives:
     - need to output align on globals, alloca
     - should output align on load, store (note: already passed to llvm.memcpy)
     - need to ensure padding is added to structures that use the "aligned" attribute

     variable-size types, shows up in:
     - iExp: will just recurse indefinitely
     - iBinop/MinusPP: will get an exception when computing elemsize
*)
open Cil
open Pretty
open List
open Llvmutils
open Llvmgen
open Llvmssa

(* Generate LLVM code (as a doc string) for file 'f'. Currently x86+gcc specific,
   and missing bitfield support (plus a few minor gcc-specific features, see above) *)
let generate (f:file) : doc = 

  (* Implementation overview:
     - For all top-level declarations except function definitions, we directly
       generate a doc string representing the LLVM equivalent.
     - For functions, we use the llvmGeneratorClass to "compile" (but the
       transformation is very simple) CIL's intermediate code to LLVM code
       (see the llvm* types in llvmgen.ml) in non-SSA form. We then use
       llvmssa.ml to transform this code into SSA form, and finally print
       the results as a doc string.
     - We also use  llvmGeneratorClass to keep track of the string constants
       used in file 'f'. We need to print these as top-level LLVM constants
       (outside function bodies).
  *)

  let globals = new llvmGeneratorClass in

  (* LLVM linkage for global 'vi' *)
  let rec gLinkage (vi:varinfo) (default:string) : string =
    match vi.vstorage with
    | Static -> " internal"
    | Extern -> " external"
    | _ -> default

  (* LLVM linkage for function 'vi' *)
  and fLinkage (vi:varinfo) : string =
    match vi.vstorage with
    | Static -> "internal "
    | Extern when vi.vinline -> "internal "
    | _ -> ""

  and gVarDecl (vi:varinfo) : doc = 
    dprintf "@@%s =%s global %a\n" vi.vname (gLinkage vi " weak") dgType vi.vtype

  and gFunctionDecl (fi:varinfo) : doc = 
    dprintf "declare %a\n" dgFunctionSig fi

  and gFunctionDef (f:fundec) : doc = 
    let hdr = dprintf "define %s%a " (fLinkage f.svar) dgFunctionSig f.svar in
    let blocks = globals#mkFunction f in
    (*fprint ~width:80 stderr ((dprintf "%s\n" f.svar.vname) ++ (globals#printBlocks () blocks));*)
    let ssaLocals = filter (fun vi -> llvmUseLocal vi) (f.sformals @ f.slocals) in
    let ssaBlocks = llvmSsa globals blocks f.sformals ssaLocals in
    hdr ++ (text "{\n") ++ (globals#printBlocks () ssaBlocks) ++ (text "}\n")

  and gStruct (ci:compinfo) : doc = 
    let pfield f = gType f.ftype in
    dprintf "%%struct.%s = type { %a }\n" ci.cname (docList pfield) ci.cfields

  (* Generate LLVM initializer from CIL initializer 'i' for type 't' *)
  and giInit (t:typ) (initexp:init) : doc = 
    let tdoc = gType t in
    let idoc = match initexp with
    | SingleInit e -> 
	(*ignore(Pretty.eprintf "%a\n" (printExp plainCilPrinter) e);*)
	globals#printValueNoType () (globals#mkConstantExp e)
    | CompoundInit (ct, inits) -> 
	if isArrayType ct then
	  (* the docs imply that we should pad the array if there are 
	     missing initializers for the tail of the array,
	     but the default frontend doesn't generate any it seems... *)
	  let ct' = typeArrayOf ct in
	  dprintf "[ %a ]" (docList (fun (o, i) -> giInit ct' i)) inits
	else (* a structure initializer *)
	  let pfield (o, fieldinit) = match o with
	  | Field(f, NoOffset) -> giInit f.ftype fieldinit
	  | _ -> raise Bug
	  in
	  dprintf "{ %a }" (docList pfield) inits
    in tdoc ++ (text " ") ++ idoc

  and gInit (t,ii) : doc = match ii.init with
  | None -> dprintf "%a zeroinitializer" dgType t
  | Some i -> giInit t i
  and dgInit () = gInit

  and gGlobal (g:global) : doc = match g with
  | GType _ -> nil
  | GCompTag (ci, _) -> gStruct ci
  | GCompTagDecl (ci, _) when not ci.cdefined -> 
      dprintf "%%struct.%s = type opaque\n" ci.cname
  | GCompTagDecl (ci, _) -> nil
  | GEnumTag _ -> nil
  | GEnumTagDecl _ -> nil
  | GVarDecl (vi, _) -> 
      if isFunctionType vi.vtype then
	gFunctionDecl vi
      else
	gVarDecl vi
  | GVar (vi, ii, _) -> dprintf "@@%s =%s global %a\n" 
	vi.vname (gLinkage vi "") dgInit (vi.vtype, ii)
  | GFun (fi, _) -> gFunctionDef fi
  | GAsm _ -> nil
  | GPragma _ -> nil
  | GText s -> text s
  in

  let body = fold_left (++) nil (map gGlobal f.globals) in
  (globals#printGlobals ()) ++ body

(* CIL feature setup *)
let feature : featureDescr = 
  { fd_name = "llvm";              
    fd_enabled = ref false;
    fd_description = "generate llvm code";
    fd_extraopt = [];
    fd_doit = 
    (function (f: file) -> 
      fprint stdout 80 (generate f));
    fd_post_check = false
  }
