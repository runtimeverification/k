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

(* Transform LLVM code output by llvmGeneratorClass#mkFunction into SSA form.
   Uses the SSA transformation algorithm described in:
     Simple Generation of Static Single-Assignment Form
     John Aycock and Nigel Horspool
     CC'2000
   (which is much simpler and essentially just as effective as the "usual", rather
   complex algorithm...)
*)

let z = 3

open Cil
open List
open Printf
open Llvmutils
open Llvmgen
open Pretty
module H = Hashtbl
module S = String

let z = 3

(* Apply the SSA transform on locals in 'ssavars' to a function whose
   body is 'bl'.  'formals' is the formal arguments to the function
   (but formals which should be subject to the SSA transform must also
   be in the 'ssavars' list). *)

let z = 3

let llvmSsa (globals:llvmGenerator) (bl:llvmBlock list) (formals:varinfo list) (ssavars:varinfo list) : llvmBlock list = 
  (* map from (b:string, v:string) -> llvmLocal
       giving the ssa variable to use for 'v' at entry to block labeled 'b' *)
  let entryName = H.create 32

  (* map from (b:string, v:string) -> llvmValue
       giving the value to use for 'v' at exit from block labeled 'b' 
     note that the result is a value as 'v' may have been assigned a constant in 'b' *)
  and exitValue = H.create 32 in

  let id = ref 0 in
  (* create a new unique LLVM local for local variable 'vi' *)
  let nextname (s:string) (t:typ) : llvmLocal = 
    id := !id + 1;
    (sprintf "%s.%d" s !id, t)
  in

  (* Rename variables 'vl' in block 'b': pick new variables for 'b' at
     entry to 'b' (except if 'b' is the function entry point), and
     rename all uses and subsequent assignments. Record the variable's
     new names at entry to 'b' and new values at exit from 'b' in
     entryName and exitValue *)
  let renameVariables (vl:varinfo list) (b:llvmBlock) : unit = 
    let blabel = b.lblabel in

    (* The entry value is a new variable for all blocks except the function entry
       point. At entry, formals keep their name in the argument list, while 
       non-formals get C's 0 value for their type (maybe LUndef would be a better
       choice?) *)
    let name1 vi = 
      if b.lbpreds <> [] then begin
	let phiname = nextname vi.vname vi.vtype in
	H.add entryName (b.lblabel, vi.vname) phiname;
	LLocal phiname
      end else if memq vi formals then 
	LLocal (vi.vname, vi.vtype)
      else
	lzero vi.vtype
    in

    (* Set initial variable values *) 
    iter (fun vi -> H.add exitValue (blabel, vi.vname) (name1 vi)) vl;

    (* Rename LLVM value 'lv' *)
    let rec renameValue (lv:llvmValue) = match lv with
    | LLocal (av, t) when H.mem exitValue (blabel, av) -> H.find exitValue (blabel, av)
    | _ -> lv

    (* Rename 'i's arguments, and remap the assigned variable if it's in vl *)
    and renameIns (i:llvmInstruction) : unit =
      i.liargs <- map renameValue i.liargs;
      match i.liresult with
      | Some (rv, t) when H.mem exitValue (blabel, rv) -> (* rv assigned, pick new name *)
	  if i.liop = LIassign then (* special assignment instruction *)
	    (* from here on, substitute rv with the value assigned *)
	    H.replace exitValue (blabel, rv) (hd i.liargs)
	  else begin
	    (* give rv a new name *)
	    let newname = nextname rv t in
	    i.liresult <- Some newname;
	    H.replace exitValue (blabel, rv) (LLocal newname)
	  end
      | _ -> ()
	    
    (* Rename in terminator 'term' *)
    and renameTerminator (term:llvmTerminator) : llvmTerminator = 
      match term with
      | TRet lv -> TRet (map renameValue lv)
      | TCond (lv, b1, b2) -> TCond (renameValue lv, b1, b2)
      | TSwitch (lv, db, cases) -> TSwitch (renameValue lv, db, cases)
      | _ -> term
    in

    iter renameIns b.lbbody;
    b.lbterminator <- renameTerminator b.lbterminator;
  in

  (* Add the phi statement for 'vi' to the start of block 'b' *)
  let addPhi (b:llvmBlock) (vi:varinfo) : unit= 
    if b.lbpreds <> [] then
      let v = vi.vname in
      let args = map (fun pb -> LPhi (H.find exitValue (pb.lblabel, v), pb)) b.lbpreds in
      let phiIns = mkIns LIphi (H.find entryName (b.lblabel, v)) args in
      b.lbbody <- phiIns :: b.lbbody
  in

  (* Optimize phi statements following Aycock & Horspool - see the paper for
     full details *)
  let optimizeSsa (bl:llvmBlock list) : unit =
    (* A union-find hash table for tracking an SSA variable's current value *)
    let varmap = H.create 32 in
    let rec remap v = 
      (*fprint ~width:80 stderr (dprintf "lookup %a\n" globals#printValue v);*)
      if H.mem varmap v then
	let v' = H.find varmap v in
	let v'' = remap v' in
	if not (llvmValueEqual v'' v') then begin
	  (*fprint ~width:80 stderr (dprintf "short %a -> %a\n" globals#printValue v globals#printValue v'');*)
	  H.replace varmap v v''
	end;
	v''
      else
	v
    in

    (* One optimization pass: remove phi-statements of the form d=phi(d, ..., d)
       and d=phi(...d or c...), in the latter case rename d to c. Note that c
       might be an LLVM value. *)
    let onepass () : bool =
      let change = ref false in
      let oneins (i:llvmInstruction) : unit = 
	if i.liop = LIphi && i.liargs <> [] then
	  let rec checkRewrite (d:llvmValue) (phiargs:llvmValue list) = 
	    match phiargs with
	    | LPhi (v, _) :: phiargs' ->
		let v' = remap v in
		if llvmValueEqual v' d then
		  checkRewrite d phiargs'
		else
		  checkCandidate d phiargs' v'
	    | [] -> i.liargs <- [] (* it's all d = phi(d, ..., d) -> nuke the phi *)
	    | _ -> ()
	  and checkCandidate (d:llvmValue) (phiargs:llvmValue list) (c:llvmValue) =
	    match phiargs with
	    | LPhi (v, _) :: phiargs' ->
		let v' = remap v in
		if llvmValueEqual v' c || llvmValueEqual v' d then
		  checkCandidate d phiargs' c
	    | [] -> (* it's all d = phi(...d or c...) -> nuke the phi and replace d by c *)
		change := true;
		(*fprint ~width:80 stderr (dprintf "remap %a -> %a, %B\n" globals#printValue d globals#printValue c (llvmValueEqual d c));*)
		H.add varmap d c;
		i.liargs <- []
	    | _ -> ()
	  in
	  checkRewrite (LLocal (getOption i.liresult)) i.liargs

      in iter (fun b -> iter oneins b.lbbody) bl;
      !change
    in

    (* After optimization, remap all variables to their final value *)
    let doremap () = 
      let rec remapval (v:llvmValue) : llvmValue = match v with
      | LLocal lv -> remap v
      | LPhi (v', b) -> LPhi (remapval v', b)
      | _ -> v
      in
      let remapterm (t:llvmTerminator) : llvmTerminator = 
	match t with
	| TRet lv -> TRet (map remapval lv)
	| TCond (lv, b1, b2) -> TCond (remapval lv, b1, b2)
	| TSwitch (lv, db, cases) -> TSwitch (remapval lv, db, cases)
	| _ -> t
      in
      let remapins (i:llvmInstruction) : unit = 
	i.liargs <- map remapval i.liargs
      in iter (fun b -> iter remapins b.lbbody; b.lbterminator <- remapterm b.lbterminator) bl
    in

    while onepass () do () done;
    doremap ()
  in

  (* Remove the phi instructions killed by optimization, and the assignment 
     statements we created during initial code generation *)
  let removeAssignAndDeadPhi (b:llvmBlock) : unit = 
    let liveins i = not (i.liop = LIassign || i.liop = LIphi && i.liargs = []) in
    b.lbbody <- filter liveins b.lbbody
  in

  iter (renameVariables ssavars) bl;
  iter (fun b -> iter (addPhi b) ssavars) bl;
  (*fprint ~width:80 stderr (dprintf "%s\n%a" "pre-opt" globals#printBlocks bl);*)
  optimizeSsa bl;
  iter removeAssignAndDeadPhi bl;
  bl
