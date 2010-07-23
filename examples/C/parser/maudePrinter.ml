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
open DefaultMaudePrinter

(* Pretty's api can be found in cil/ocamlutil/pretty.mli *)

let (+^) (d1:Pretty.doc) (d2:string) : Pretty.doc = d1 ++ text d2
let (^+) (d1:string) (d2:Pretty.doc) : Pretty.doc = text d1 ++ d2
let sp : Pretty.doc = (text " ")

let paren (d:Pretty.doc) : Pretty.doc = "(" ^+ d +^ ")"
let giveType (d1:Pretty.doc) (d2:string) : Pretty.doc = paren(d1) ++ (text d2)
let wrap (d1:Pretty.doc) (d2:string) : Pretty.doc = d2 ^+ paren(d1)

let wrapifne (d1:Pretty.doc) (d2:string) = 
	if (d1 = nil) then nil else wrap d1 d2

let replace input output =
    Str.global_replace (Str.regexp_string input) output
let noscores s = 
	(replace "_" "u" s)
(* val replace : string -> string -> string -> string = <fun> *)


(* let trim (s:string) : string = String.sub s 1 ((String.length s) - 1) *)

class maudePrinter = object(self)
	inherit defaultMaudePrinterClass as super
	
	(** Invoked for each variable declaration. Note that variable 
     * declarations are all the [GVar], [GVarDecl], [GFun], all the [varinfo] 
     * in formals of function types, and the formals and locals for function 
     * definitions. *)
	method pVDecl () (v:varinfo) = wrapifne (super#pVDecl () v) "Declaration"
	
	(** Print a block. *)
	method pBlock () (b:block) = wrap (super#pBlock () b) "Block"
    
    (** A field declaration *)
	method pFieldDecl () (f:fieldinfo) = wrap (super#pFieldDecl () f) "Field"
	
    (** Print initializers. This can be slow and is used by {!Cil.printGlobal} *)
	(*method pInit () (i:init) = wrap (super#pInit () i) "Initializer"*)
	method pInit () (i:init) = (super#pInit () i)
    (** Invoked on each instruction occurrence. *)
	(* method pInstr () (i:instr) = wrap (super#pInstr () i) "Instruction" *)

	(** Invoked on each lvalue occurrence *)
    method pLval () (l:lval) = paren (super#pLval () l)
	(* method pLval () (l:lval) = wrap (super#pLval () l) "lval" *)
	
    (** Control-flow statement.  *)
	(* method pStmt () (s:stmt) = wrap (super#pStmt () s) "ControlFlowStatement" *)
	
	(** Print a statement kind. The code to be printed is given in the
	     * {!Cil.stmtkind} argument.  The initial {!Cil.stmt} argument
	     * records the statement which follows the one being printed;
	     * {!Cil.defaultCilPrinterClass} uses this information to prettify
	     * statement printing in certain special cases. *)
	(* method pStmtKind (s:stmt) () (k:stmtkind) = wrap (super#pStmtKind s () k) "StatementKind" *)
    
	(** Use of some type in some declaration. The first argument is used to print 
		* the declared element, or is None if we are just printing a type with no 
		* name being declared. Note that for structure/union and enumeration types 
		* the definition of the composite type is not visited. Use [vglob] to 
		* visit it.  *)
	
	(*method pType (d:Pretty.doc option) () (t:typ) = wrap (super#pType d () t) "Type"*)
	method pType (d:Pretty.doc option) () (t:typ) = text (noscores (sprint 1000 (super#pType d () t)))
	(*method pType (d:Pretty.doc option) () (t:typ) = paren (super#pType d () t) *)
	 (*method pType (d:Pretty.doc option) () (t:typ) = 
		(* wrap (super#pType d () t) "Type" *)
		match d with 
			| None -> (super#pType d () t)
			| Some _ -> wrap (super#pType d () t) "DeclaratorAux"*)
			
	(** Attribute lists *)
     (* method pAttrs () (a:attributes) = wrap (super#pAttrs () a) "Attributes" *)
	 method pAttrs () (a:attributes) = nil
	
    (** Print expressions *) 
	method pExp () (e:exp) = paren (super#pExp () e)
	
	(** Invoked on each variable use. *)
	(* method pVar (v:varinfo) = (super#pVar v) *)
	method pVar (v:varinfo) = text (noscores (sprint 1000 (super#pVar v)))

	(** Global (vars, types, etc.). This can be slow and is used only by 
     * {!Cil.printGlobal} but not by {!Cil.dumpGlobal}. *)
	method pGlobal () (g:global) = wrap (super#pGlobal () g) "Global"
   
(*
  

  method pOffset: Pretty.doc -> offset -> Pretty.doc
    (** Invoked on each offset occurrence. The second argument is the base. *)

  method pLabel: unit -> label -> Pretty.doc
    (** Print a label. *)

  method pAttr: attribute -> Pretty.doc * bool
    (** Attribute. Also return an indication whether this attribute must be 
      * printed inside the __attribute__ list or not. *)
   
  method pAttrParam: unit -> attrparam -> Pretty.doc 
    (** Attribute parameter *)
   


  method pLineDirective: ?forcefile:bool -> location -> Pretty.doc
    (** Print a line-number. This is assumed to come always on an empty line. 
     * If the forcefile argument is present and is true then the file name 
     * will be printed always. Otherwise the file name is printed only if it 
     * is different from the last time time this function is called. The last 
     * file name is stored in a private field inside the cilPrinter object. *)


*)	
end

