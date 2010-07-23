(*
 *
 * Copyright (c) 2007, 
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


(** This module provides inlining functions. You can run it from the cilly 
 * command line by passing the names of the functions to inline:
 * 
 *    cilly --save-temps --inline=toinline module.c
 * 
 * This module has not been tested extensively, so you should run it with 
 * the --check argument to ensure that it does not break any CIL invariants 
 *
 * 
 * You can also call directly the [doFile] and [doFunction] functions.
 
 *)

open Pretty
open Cil
module E = Errormsg
module H = Hashtbl
module IH = Inthash
module A = Alpha

let doInline = ref false
let debug = true

exception Recursion (* Used to signal recursion *)

(* A visitor that makes a deep copy of a function body for use inside a host 
 * function, replacing duplicate labels, returns, etc. *)
class copyBodyVisitor     (host: fundec)                (* The host of the 
                                                         * inlining *) 
                          (inlining: varinfo)           (* Function being 
                                                         * inlined *)
                          (replVar: varinfo -> varinfo) (* Maps locals of the 
                                                         * inlined function 
                                                         * to locals of the 
                                                         * host *)
                          (retlval: varinfo option)     (* The destination 
                                                         * for the "return" *)
                          (replLabel: string -> string)  
                                                        (* A renamer for 
                                                         * labels *)
                          (retlab: stmt)                (* The label for the 
                                                         * return *)
                          = object (self)
  inherit nopCilVisitor

      (* Keep here a maping from statements to their copies, indexed by their 
       * original ID *)
  val stmtmap : stmt IH.t = IH.create 113

      (* Keep here a list of statements to be patched *)
  val patches : stmt list ref = ref []

  val argid = ref 0

      (* This is the entry point *)
  method vfunc (f: fundec) : fundec visitAction = 
    let patchfunction (f' : fundec) = 
      let findStmt (i: int) = 
        try IH.find stmtmap i 
        with Not_found -> E.s (bug "Cannot find the copy of stmt#%d" i)
      in
      E.log "Patching gotos\n";
      let patchstmt (s: stmt) = 
        match s.skind with
          Goto (sr, l) -> 
            if debug then
              E.log "patching goto\n";
            (* Make a copy of the reference *)
            let sr' = ref (findStmt !sr.sid) in
            s.skind <- Goto (sr',l)
        | Switch (e, body, cases, l) -> 
            s.skind <- Switch (e, body, 
                               Util.list_map (fun cs -> findStmt cs.sid) cases, l)
        | _ -> ()
      in
      List.iter patchstmt !patches;
      f'
    in
    patches := [];
    IH.clear stmtmap;
    ChangeDoChildrenPost (f, patchfunction)
    
      (* We must replace references to local variables *)
  method vvrbl (v: varinfo) = 
    if v.vglob then 
      SkipChildren 
    else 
      let v' = replVar v in 
      if v == v' then 
        SkipChildren
      else
        ChangeTo v'


  method vinst (i: instr) = 
    match i with 
      Call (_, Lval (Var vi, _), _, _) when vi.vid == inlining.vid -> 
        raise Recursion

    | _ -> DoChildren

        (* Replace statements. *)
  method vstmt (s: stmt) : stmt visitAction = 
    (* There is a possibility that we did not have the statements IDed 
     * propertly. So, we change the ID even on the replaced copy so that we 
     * can index on them ! *)
    (match host.smaxstmtid with 
      Some id ->
        s.sid <- 1 + id
    | None -> 
        s.sid <- 1);
    (* Copy and change ID *)
    let s' = {s with sid = s.sid} in
    host.smaxstmtid <- Some s'.sid;

    IH.add stmtmap s.sid s'; (* Remember where we copied this statement *)
    (* if we have a Goto or a Switch remember them to fixup at end *)
    (match s'.skind with
      (Goto _ | Switch _) -> 
        E.log "Found goto\n";
        patches := s' :: !patches
    | _ -> ());
    
    (* Change the returns *)
    let postProc (s': stmt) : stmt = 
      (* Rename the labels if necessary *)
      s'.labels <- 
        Util.list_map (fun lb -> 
          match lb with
            Label (n, l, fromsrc) -> Label(replLabel n, l, fromsrc)
          | _ -> lb) s'.labels;

      (* Now deal with the returns *)
      (match s'.skind with 
      | Return (ro, l) -> begin
          (* Change this into an assignment followed by a Goto *)
          match ro, retlval with 
            _, None -> (* Function called with no return lval *)
              s'.skind <- Goto (ref retlab, l)
                
          | None, _ -> 
              ignore (warn "Found return without value in inlined function");
              s'.skind <- Goto (ref retlab, l)
                
          | Some rv, Some retvar-> 
              s'.skind <-
                Block (mkBlock [ mkStmt (Instr [(Set (var retvar, rv, l))]);
                                 mkStmt (Goto (ref retlab, l)) ])
      end
      | _ -> ());
      s'
    in
            (* Do the children then postprocess *)
    ChangeDoChildrenPost (s', postProc)

      (* Copy blocks since they are mutable *)
  method vblock (b: block) = 
    ChangeDoChildrenPost ({b with bstmts = b.bstmts}, fun x -> x)


  method vglob _ = E.s (bug "copyFunction should not be used on globals")
end

(** Replace a statement with the result of inlining *)
let replaceStatement (host: fundec)                         (* The host *)
                     (inlineWhat: varinfo -> fundec option) (* What to inline *)
                     (replLabel: string -> string)          (* label 
                                                             * replacement *)
                     (anyInlining: bool ref)                (* will set this 
                                                             * to true if we 
                                                             * did any 
                                                             * inlining *)
                     (s: stmt) : stmt = 
  match s.skind with 
    Instr il when il <> [] -> 
      let prevrstmts: stmt list ref = ref [] in (* Reversed list of previous 
                                                 * statements *)
      let prevrinstr: instr list ref = ref [] in (* Reverse list of previous 
                                                  * instructions, in this 
                                                  * statement *)
      let emptyPrevrinstr () = 
        if !prevrinstr <> [] then begin
          prevrstmts := mkStmt (Instr (List.rev !prevrinstr)) :: !prevrstmts;
          prevrinstr := []
        end
      in
        
      let rec loop (rest: instr list)      (* Remaining instructions *)
          : unit = 
        match rest with 
          [] -> (* Done *) ()

        | (Call (lvo, Lval (Var fvi, NoOffset), args, l) as i) :: resti -> begin
            if debug then 
              E.log "Checking whether to inline %s\n" fvi.vname;
            let replo: fundec option = 
              match inlineWhat fvi with 
                Some repl -> 
                  if repl.svar.vid = host.svar.vid then begin
                    ignore (warn "Inliner encountered recursion in inlined function %s" 
                              host.svar.vname);
                    None
                  end else
                    Some repl
              | None -> None
            in
           match replo with  
           | None -> prevrinstr := i :: !prevrinstr;
               loop resti
                 
           | Some repl -> begin
               anyInlining := true;
               E.log "Done inlining\n";

               (* We must inline *)
               (* Prepare the mapping of local variables *)
               let vmap : varinfo IH.t = IH.create 13 in 
               let replVar (vi: varinfo) = 
                 if vi.vglob then vi
                 else 
                   try IH.find vmap vi.vid
                   with Not_found -> begin
                     E.s (bug "Cannot find the new copy of local variable %s" 
                            vi.vname)
                   end
               in
               (* Do the actual arguments, and keep extending prevrinstr *)
               let rec loopArgs (args: exp list) (formals: varinfo list) = 
                 match args, formals with 
                   [], [] -> ()
                 | (a :: args'), (f :: formals') -> begin
                     (* We must copy the argument even if it is already a 
                      * variable, to obey call by value *)
                     (* Make a local and a copy *)
                     let f' = makeTempVar host ~name:f.vname f.vtype in
                     prevrinstr := (Set (var f', a, l)) :: !prevrinstr;
                     IH.add vmap f.vid f';
                     
                     loopArgs args' formals'
                 end
                 | _, _ -> E.bug "Invalid number of arguments"
               in
               loopArgs args repl.sformals;
               
               (* Copy the locals *)
               List.iter (fun loc -> 
                 let loc' = makeTempVar host ~name:loc.vname loc.vtype in 
                 IH.add vmap loc.vid loc') repl.slocals;
               
               
               (* Make the return statement *)
               let (ret : stmt), (retvar: varinfo option) = 
                 let rt, _, isva, _ = splitFunctionType repl.svar.vtype in
                 match rt with 
                   TVoid _  -> mkStmt (Instr []), None
                 | _ -> begin
                     match lvo with 
                       None -> mkStmt (Instr []), None
                     | Some lv -> 
                         (* Make a return variable *)
                         let rv = makeTempVar 
                             host ~name:("ret_" ^ repl.svar.vname) rt in
                         mkStmtOneInstr (Set (lv, Lval (var rv), l)), Some rv
                 end
               in
               ret.labels <- [Label (replLabel ("Lret_" ^ repl.svar.vname),
                                     l, false)];
               let oldBody = repl.sbody in 
               (* Now replace the body *)
               (try
                 ignore (visitCilFunction 
                           (new copyBodyVisitor host repl.svar replVar 
                              retvar replLabel ret) 
                           repl);
                 currentLoc := l;
                 let body' = repl.sbody in 
                 (* Replace the old body in the function to inline *)
                 repl.sbody <- oldBody;
                 
                 emptyPrevrinstr ();
                 prevrstmts := ret :: (mkStmt (Block body')) :: !prevrstmts
               with Recursion -> 
                 ignore (warn "Encountered recursion in function %s" 
                           repl.svar.vname);
                 prevrinstr := i :: !prevrinstr);

               loop resti
           end
        end
        | i :: resti -> 
            prevrinstr := i :: !prevrinstr; 
            loop resti
      in
      loop il;

      emptyPrevrinstr ();
      if List.length !prevrstmts > 1 then 
        s.skind <- Block (mkBlock (List.rev !prevrstmts));

      s

  | _ -> s
            
            
(** Apply inlining to a function, modify in place *)
let doFunction  (host: fundec) (* The function into which to inline *)
                (inlineWhat: varinfo -> fundec option) (* The functions to 
                                                        * inline, as a 
                                                        * partial map 
                                                        * from varinfo to 
                                                        * body *)
                (anyInlining: bool ref)                (* Will be set to true 
                                                        * if any inlining 
                                                        * took place *)
    : unit = 
  if debug then 
    E.log "Doing inlining for %s\n" host.svar.vname;

  (* Scan the host function and build the alpha-conversion table for labels *)
  let labTable: (string, unit A.alphaTableData ref) H.t = H.create 5 in
  ignore (visitCilBlock 
            (object 
              inherit nopCilVisitor
              method vstmt (s: stmt) = 
                List.iter 
                  (fun l ->
                    match l with 
                      Label(ln, _, _) -> 
                        ignore (A.registerAlphaName ~alphaTable:labTable 
                                  ~undolist:None ~data:() ~lookupname:ln)
                    | _ -> ())
                  s.labels;
                DoChildren
                  
            end)
            host.sbody);
  (* Now the label replacement function *)
  let replLabel (ln: string) : string = 
    let ln', _ = A.newAlphaName 
        ~alphaTable:labTable ~undolist:None ~lookupname:ln ~data:() in
    ln'
  in
  (* Now scan the function to do the inlining *)
  let body' : block = 
    visitCilBlock (object
      inherit nopCilVisitor
      method vstmt (s: stmt) = 
        ChangeDoChildrenPost (s, 
                              replaceStatement host inlineWhat 
                                replLabel anyInlining)
    end) host.sbody in 
  host.sbody <- body';
  ()


(** Apply inlining to a whole file *)
let doFile (inlineWhat: varinfo -> fundec option) (* What to inline. See 
                                                   * comments for [doFunction] *)
           (fl: file) = 
  iterGlobals fl (fun g -> 
    match g with 
      GFun(fd, l) -> 
        (* Keep doing inlining until there is no more. We will catch 
         * recursion eventually when we want to inline a function into itself*) 
        let anyInlining = ref true in
        while !anyInlining do
          anyInlining := false;
          doFunction fd inlineWhat anyInlining
        done

    | _ -> ())
    

(* Function names to inline *)
let toinline: string list ref = ref []
let doit (fl: file) = 
  (* Scan the file and build the hashtable of functions to inline *)
  let inlineTable: (string, fundec) H.t = H.create 5 in 
  visitCilFile (object
    inherit nopCilVisitor
    method vfunc (fd: fundec) =
      if List.mem fd.svar.vname !toinline then 
        H.add inlineTable fd.svar.vname fd;
      SkipChildren
  end) fl;
  let inlineWhat (vi: varinfo) : fundec option = 
    try Some (H.find inlineTable vi.vname)
    with Not_found -> None
  in
  (* Give warnings if we cannot find some fundecs *)
  List.iter (fun fn -> 
    if not (H.mem inlineTable fn) then 
      ignore (warn "Cannot inline function %s because we cannot find its definition" fn))
    !toinline;

  doFile inlineWhat fl

let feature : featureDescr = 
  { fd_name = "inliner";
    fd_enabled = doInline;
    fd_description = "inline function calls";
    fd_extraopt = [
    "--inline", Arg.String (fun s -> doInline := true;
                                     toinline := s :: !toinline), 
                "<func> inline this function";
    ];
    fd_doit = doit;
    fd_post_check = true;
  } 

