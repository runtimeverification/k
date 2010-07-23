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

let replace input output =
    Str.global_replace (Str.regexp_string input) output

let noscores s = 
	(replace "_" "u" s)

class maudeVisitor = object (self) inherit nopCilVisitor
	val mutable identifierList : string list = []
	val mutable typedefList : string list = []
	
	method getIdentifierList = identifierList
	method getTypedefList = typedefList
	
	method vvdec (v:varinfo) = begin
		(*print_string (v.vname ^ "\n");*)
		(*if (v.vname <> "main") then (v.vname <- v.vname ^ (string_of_int v.vid));*)
		identifierList <- (noscores v.vname) :: identifierList;
		DoChildren
	end

	method vvrbl (v:varinfo) = begin
		identifierList <- (noscores v.vname) :: identifierList;
		DoChildren
	end
	
	method vglob (g:global) = begin
		( match g with 
			| GEnumTag (enum, _) -> 
				identifierList <- (noscores enum.ename) :: identifierList ;
		      (* Do the values and attributes of the enumerated items *)
		      let itemVisit (name, exp, loc) = 
				identifierList <- (noscores name) :: identifierList in
		      List.iter itemVisit enum.eitems;
			| GType(typeinfo, location) -> typedefList <- (noscores typeinfo.tname) :: typedefList
			| GVar(varinfo, initinfo, _) ->
				(match initinfo.init with
					| None -> (
						match varinfo.vtype with
						| TArray(_, _, _) 
						| TComp(_, _)
						| TInt (_, _)
						| TFloat (_, _)
						| TPtr _
						| TEnum _
							-> initinfo.init <- Some(makeZeroInit varinfo.vtype);
						| _ -> ()
					);
					| _ -> ();
				)
				
			| GVarDecl(varinfo, location) -> 
				identifierList <- (noscores varinfo.vname) :: identifierList
			| GCompTag (comp, l) -> begin
				identifierList <- (noscores comp.cname) :: identifierList;
				let fieldVisit = fun fi -> 
					(* print_string (fi.fname ^ "\n"); *)
					identifierList <- (noscores fi.fname) :: identifierList
			      in
			      List.iter fieldVisit comp.cfields;
			end
			
			| _ -> ()
		) ;
		DoChildren
	end
	
	method vstmt (s: stmt) : stmt visitAction = 
		let labelVisit = fun fi -> match fi with 
			| Label (s, _, true) -> identifierList <- (noscores s) :: identifierList
			| Label (s, _, false) -> identifierList <- (noscores s) :: identifierList	
			| _ -> ()
		in List.iter labelVisit s.labels;
		DoChildren
		
	method vinit (forg: varinfo) (off: offset) (i:init) = begin
		identifierList <- (noscores forg.vname) :: identifierList;
		DoChildren
	end
	
	method vtype (t:typ) = begin
		( match t with 
			| TFun (restyp, args, isvararg, a) -> begin
				let argVisit = fun fi -> 
					match fi with
					| (aname, atype, aattr) -> 
						if (String.length(aname) != 0) then (
							identifierList <- (noscores aname) :: identifierList;
						)
			      in match args with
					| Some xs -> List.iter argVisit xs
					| None -> () ;
			end
			| _ -> ()
		) ;
		DoChildren
	end
	
	
end
