(*
 *
 * Copyright (c) 2001-2003, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 *  Simon Goldsmith     <sfg@cs.berkeley.edu>
 *  S.P Rahul, Aman Bhargava
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

(* Authors: Aman Bhargava, S. P. Rahul *)
(* sfg: this stuff was stolen from optim.ml - the code to print the cfg as
   a dot graph is mine *)

open Pretty
open Cil
module E=Errormsg

(* entry points: cfgFun, printCfgChannel, printCfgFilename *)

(* known issues:
 * -sucessors of if somehow end up with two edges each 
 *)

(*------------------------------------------------------------*)
(* Notes regarding CFG computation:
   1) Initially only succs and preds are computed. sid's are filled in
      later, in whatever order is suitable (e.g. for forward problems, reverse
      depth-first postorder).
   2) If a stmt (return, break or continue) has no successors, then
      function return must follow.
      No predecessors means it is the start of the function
   3) We use the fact that initially all the succs and preds are assigned []
*)

(* Fill in the CFG info for the stmts in a block
   next = succ of the last stmt in this block
   break = succ of any Break in this block
   cont  = succ of any Continue in this block
   None means the succ is the function return. It does not mean the break/cont
   is invalid. We assume the validity has already been checked.
*)

let start_id = ref 0 (* for unique ids across many functions *)

class caseLabeledStmtFinder slr = object(self)
    inherit nopCilVisitor
    
    method vstmt s =
        if List.exists (fun l ->
            match l with | Case(_, _) | Default _ -> true | _ -> false)
            s.labels
        then begin
            slr := s :: (!slr);
            match s.skind with
            | Switch(_,_,_,_) -> SkipChildren
            | _ -> DoChildren
        end else match s.skind with
        | Switch(_,_,_,_) -> SkipChildren
        | _ -> DoChildren
end

let findCaseLabeledStmts (b : block) : stmt list =
    let slr = ref [] in
    let vis = new caseLabeledStmtFinder slr in
    ignore(visitCilBlock vis b);
    !slr

(* entry point *)

(** Compute a control flow graph for fd.  Stmts in fd have preds and succs
  filled in *)
let rec cfgFun (fd : fundec): int = 
  begin
    let initial_id = !start_id in
    let nodeList = ref [] in

    cfgBlock fd.sbody None None None nodeList;

    fd.smaxstmtid <- Some(!start_id);
    fd.sallstmts <- List.rev !nodeList;

    !start_id - initial_id
  end


and cfgStmts (ss: stmt list) 
             (next:stmt option) (break:stmt option) (cont:stmt option)
             (nodeList:stmt list ref) =
  match ss with
    [] -> ();
  | [s] -> cfgStmt s next break cont nodeList
  | hd::tl ->
      cfgStmt hd (Some (List.hd tl))  break cont nodeList;
      cfgStmts tl next break cont nodeList

and cfgBlock  (blk: block) 
              (next:stmt option) (break:stmt option) (cont:stmt option)
              (nodeList:stmt list ref) =
   cfgStmts blk.bstmts next break cont nodeList


(* Fill in the CFG info for a stmt
   Meaning of next, break, cont should be clear from earlier comment
*)
and cfgStmt (s: stmt) (next:stmt option) (break:stmt option) (cont:stmt option)
            (nodeList:stmt list ref) =
  incr start_id;
  s.sid <- !start_id;
  nodeList := s :: !nodeList; (* Future traversals can be made in linear time. e.g.  *)
  if s.succs <> [] then begin
    (*E.s*)ignore (bug "CFG must be cleared before being computed!");
	raise (Failure "CFG bug")
  end;
  let addSucc (n: stmt) =
    if not (List.memq n s.succs) then
      s.succs <- n::s.succs;
    if not (List.memq s n.preds) then
      n.preds <- s::n.preds
  in
  let addOptionSucc (n: stmt option) =
    match n with
      None -> ()
    | Some n' -> addSucc n'
  in
  let addBlockSucc (b: block) (n: stmt option) =
    (* Add the first statement in b as a successor to the current stmt.
       Or, if b is empty, add n as a successor *)
    match b.bstmts with
      [] -> addOptionSucc n
    | hd::_ -> addSucc hd
  in
  let instrFallsThrough (i : instr) : bool = match i with
      Call (_, Lval (Var vf, NoOffset), _, _) -> 
        (* See if this has the noreturn attribute *)
        not (hasAttribute "noreturn" vf.vattr)
    | Call (_, f, _, _) -> 
        not (hasAttribute "noreturn" (typeAttrs (typeOf f)))
    | _ -> true
  in
  match s.skind with
    Instr il  -> 
      if List.for_all instrFallsThrough il then
        addOptionSucc next
      else
        ()
  | Return _  -> ()
  | Goto (p,_) -> addSucc !p
  | Break _ -> addOptionSucc break
  | Continue _ -> addOptionSucc cont
  | If (_, blk1, blk2, _) ->
      (* The succs of If is [true branch;false branch] *)
      addBlockSucc blk2 next;
      addBlockSucc blk1 next;
      cfgBlock blk1 next break cont nodeList;
      cfgBlock blk2 next break cont nodeList
  | Block b -> 
      addBlockSucc b next;
      cfgBlock b next break cont nodeList
  | Switch(_,blk,l,_) ->
      let bl = findCaseLabeledStmts blk in
      List.iter addSucc (List.rev bl(*l*)); (* Add successors in order *)
      (* sfg: if there's no default, need to connect s->next *)
      if not (List.exists 
                (fun stmt -> List.exists 
                   (function Default _ -> true | _ -> false)
                   stmt.labels) 
                bl) 
      then 
        addOptionSucc next;
      cfgBlock blk next next cont nodeList
  | Loop(blk, loc, s1, s2) ->
      s.skind <- Loop(blk, loc, (Some s), next);
      addBlockSucc blk (Some s);
      cfgBlock blk (Some s) next (Some s) nodeList
      (* Since all loops have terminating condition true, we don't put
         any direct successor to stmt following the loop *)
  | TryExcept _ | TryFinally _ -> 
      E.s (E.unimp "try/except/finally")

(*------------------------------------------------------------*)

(**************************************************************)
(* do something for all stmts in a fundec *)

let rec forallStmts (todo) (fd : fundec) = 
  begin
    fasBlock todo fd.sbody;
  end

and fasBlock (todo) (b : block) =
  List.iter (fasStmt todo) b.bstmts

and fasStmt (todo) (s : stmt) =
  begin
    ignore(todo s);
    match s.skind with
      | Block b -> fasBlock todo b
      | If (_, tb, fb, _) -> (fasBlock todo tb; fasBlock todo fb)
      | Switch (_, b, _, _) -> fasBlock todo b
      | Loop (b, _, _, _) -> fasBlock todo b
      | (Return _ | Break _ | Continue _ | Goto _ | Instr _) -> ()
      | TryExcept _ | TryFinally _ -> E.s (E.unimp "try/except/finally")
  end
;;

(**************************************************************)
(* printing the control flow graph - you have to compute it first *)

let d_cfgnodename () (s : stmt) =
  dprintf "%d" s.sid

let d_cfgnodelabel () (s : stmt) =
  let label = 
  begin
    match s.skind with
      | If (e, _, _, _)  -> "if" (*sprint ~width:999 (dprintf "if %a" d_exp e)*)
      | Loop _ -> "loop"
      | Break _ -> "break"
      | Continue _ -> "continue"
      | Goto _ -> "goto"
      | Instr _ -> "instr"
      | Switch _ -> "switch"
      | Block _ -> "block"
      | Return _ -> "return"
      | TryExcept _ -> "try-except"
      | TryFinally _ -> "try-finally"
  end in
    dprintf "%d: %s" s.sid label

let d_cfgedge (src) () (dest) =
  dprintf "%a -> %a"
    d_cfgnodename src
    d_cfgnodename dest

let d_cfgnode () (s : stmt) =
    dprintf "%a [label=\"%a\"]\n\t%a" 
    d_cfgnodename s
    d_cfgnodelabel s
    (d_list "\n\t" (d_cfgedge s)) s.succs

(**********************************************************************)
(* entry points *)

(** print control flow graph (in dot form) for fundec to channel *)
let printCfgChannel (chan : out_channel) (fd : fundec) =
  let pnode (s:stmt) = fprintf chan "%a\n" d_cfgnode s in
    begin
      ignore (fprintf chan "digraph CFG_%s {\n" fd.svar.vname);
      forallStmts pnode fd;
      ignore(fprintf chan  "}\n");
    end

(** Print control flow graph (in dot form) for fundec to file *)
let printCfgFilename (filename : string) (fd : fundec) =
  let chan = open_out filename in
    begin
      printCfgChannel chan fd;
      close_out chan;
    end


;;

(**********************************************************************)


let clearCFGinfo (fd : fundec) =
  let clear s =
    s.sid <- -1;
    s.succs <- [];
    s.preds <- [];
  in
  forallStmts clear fd

let clearFileCFG (f : file) =
  start_id := 0;
  iterGlobals f (fun g ->
    match g with GFun(fd,_) ->
      clearCFGinfo fd
    | _ -> ())

let computeFileCFG (f : file) =
  iterGlobals f (fun g ->
    match g with GFun(fd,_) ->
      ignore(cfgFun fd)
    | _ -> ())

let allStmts (f : file) : stmt list =
  foldGlobals f
    (fun accu g ->
      match g with
      | GFun (f,l) -> f.sallstmts @ accu
      | _ -> accu
    ) []
