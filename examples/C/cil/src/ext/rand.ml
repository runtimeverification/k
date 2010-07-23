(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 *  Sumit Gulwani       <gulwani@cs.berkeley.edu>
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

open Pretty
open Cil
module E = Errormsg
module H = Hashtbl

let enabled = ref false


(** This is some testing code for polynomial encoding of trees *)


(* A tree with named leaves *)
type tree = Leaf of string | Node of tree * tree


(* A polynomial is a list of leaf * monomial. A monomial is a sorted list of 
 * variables. *)
type mono  = int list 
type poly  = (string * mono) list


(* Multiply a monomial by a variable. Keep the monomial sorted *)
let rec varTimesMono (v: int) (m: mono) = 
  match m with 
    [] -> [v]
  | v' :: rest when v' >= v -> v :: m
  | v' :: rest -> v' :: varTimesMono v rest
 
(* Multiply a polynomial by a variable *)
let varTimesPoly (v: int) (p: poly) : poly = 
  Util.list_map (fun (l, m) -> (l, varTimesMono v m)) p


(* Add a number of polynomials *)
let addPoly (pl : poly list) = List.concat pl


(* Group a polynomial by leaf *)
let groupByLeaf (p: poly) : (string * mono list) list = 
  let h: (string, mono) H.t = H.create 127 in
  let leaves: (string, unit) H.t = H.create 13 in
  List.iter 
    (fun (l, m) -> 
      H.replace leaves l ();
      H.add h l m)
    p;
  (* Sort the leaves *)
  let ll = H.fold (fun l _ acc -> l :: acc) leaves [] in
  let ll = List.sort (fun l1 l2 -> compare l1 l2) ll in
  Util.list_map 
    (fun l -> 
      let ml = H.find_all h l in
      (l, ml))
    ll
      

(* Group a polynomial by monomials *)
let groupByMonomial (p: poly) : (mono * string list) list = 
  let h: (mono, string) H.t = H.create 127 in
  let monomials: (mono, unit) H.t = H.create 13 in
  List.iter 
    (fun (l, m) -> 
      H.replace monomials m ();
      H.add h m l)
    p;
  (* Sort the monomials *)
  let ml = H.fold (fun m _ acc -> m :: acc) monomials [] in
  let ml = List.sort (fun l1 l2 -> compare l1 l2) ml in
  Util.list_map 
    (fun m -> 
      let ll = H.find_all h m in
      let ll = List.sort compare ll in
      (m, ll))
    ml

let docMono (m: mono) : doc = 
  let rec loop (v: int) (degree: int) (rest: mono) : doc = 
    match rest with
      v' :: rest' when v = v' -> loop v (degree + 1) rest'
    | _ -> 
        let this = 
          if degree = 1 then 
            dprintf "V%d" v
          else
            dprintf "V%d^%d" v degree
        in
        this ++
          (match rest with 
            v :: rest -> loop v 1 rest
          | [] -> nil)
  in
  match m with 
    [] -> num 1
  | v :: rest -> loop v 1 rest
    
let printPolyByLeaf (p: poly) = 
  let poly' = groupByLeaf p in
  List.iter
    (fun (l, ml) -> 
      ignore (E.log " %s * (@[%a@]) +\n"
                l (docList (chr '+' ++ break) docMono) ml))
    poly'

let printPolyByMonomial (p: poly) = 
  let poly' = groupByMonomial p in
  List.iter
    (fun (m, ll) -> 
      ignore (E.log " %a * (@[%a@]) +\n"
                insert (docMono m)
                (docList (chr '+' ++ break) text) ll))
    poly'
    

(* Solve a polynomial to find the leaves *)
let solved: (string, unit) H.t = H.create 17
let nrSolved = ref 0
let rec solve (p: poly) = 
  let solvedOne = ref false in
  (* Find the monos with singletons *)
  let rec solveMono
      (mono: (mono * string list))
      (acc : (mono * string list) list)
      : (mono * string list) list 
      = 
    let m, vl = mono in
    (* Find how many unsolved variables we have for this monomial *)
    let unsolved = List.filter (fun v -> not (H.mem solved v)) vl in
    match unsolved with 
      [] -> (* Drop it *) acc
    | [v] -> (* One new variable *)
        ignore (E.log "Solved %s\n" v);
        solvedOne := true;
        H.add solved v ();
        (* Drop this monomial *)
        acc
    | _ -> (m, unsolved) :: acc
  in
  H.clear solved;
  nrSolved := 0;
  let rec repeat (m: (mono * string list) list) = 
    solvedOne := false;
    let m' = 
      List.fold_left
        (fun acc m -> solveMono m acc)
        []
        m
    in
    if m' = [] then 
      ignore (E.log "That worked\n")
    else 
      if !solvedOne then repeat m' else begin
        ignore (E.log "Got stuck with:\n");
        List.iter
          (fun (m, ll) -> 
            ignore (E.log " %a * (@[%a@]) +\n"
                      insert (docMono m)
                      (docList (chr '+' ++ break) text) ll))
          m'
      end
  in
  repeat (groupByMonomial p)

(* Evaluate the ith polynomial for a tree *)
let rec eval2 (i: int) (t: tree)  = 
  match i, t with 
    _, Leaf l -> [(l, [])]
  | 1, Node (t1, t2) -> 
      addPoly [ varTimesPoly 0 (eval2 1 t1);
                varTimesPoly 0 (eval2 1 t2);
                varTimesPoly 1 (eval2 2 t1);
                varTimesPoly 2 (eval2 2 t2) ]
  | 2, Node(t1, t2) -> 
      addPoly [ eval2 2 t1; 
                eval2 2 t2 ]
  | _ -> E.s (bug "eval2")


let rec eval2m (i: int) (t: tree)  = 
  match i, t with 
    _, Leaf l -> [(l, [])]
  | 1, Node (t1, t2) -> 
      addPoly [ varTimesPoly 0 (eval2m 1 t1);
                varTimesPoly 1 (eval2m 1 t2);
                varTimesPoly 2 (eval2m 2 t1);
                varTimesPoly 3 (eval2m 2 t2) ]
  | 2, Node(t1, t2) -> 
      addPoly [ varTimesPoly 4 (eval2m 2 t1); 
                varTimesPoly 5 (eval2m 2 t2) ]
  | _ -> E.s (bug "eval2m")

let rec eval2t (i: int) (t: tree)  = 
  match i, t with 
    _, Leaf l -> [(l, [])]
  | 1, Node (t1, t2) -> 
      addPoly [ varTimesPoly 0 (eval2t 1 t1);
                varTimesPoly 1 (eval2t 1 t2);
                varTimesPoly 2 (eval2t 2 t1);
                varTimesPoly 3 (eval2t 2 t2) ]
  | 2, Node(t1, t2) -> 
      addPoly [ varTimesPoly 4 (eval2t 1 t1); 
                varTimesPoly 5 (eval2t 1 t2);
                varTimesPoly 6 (eval2t 2 t1); 
                varTimesPoly 7 (eval2t 2 t2) ]
  | _ -> E.s (bug "eval2m")

let rec eval3t (i: int) (t: tree)  = 
  match i, t with 
    _, Leaf l -> [(l, [])]
  | 1, Node (t1, t2) -> 
      addPoly [ varTimesPoly 0 (eval3t 1 t1);
                varTimesPoly 1 (eval3t 1 t2);
                varTimesPoly 2 (eval3t 2 t1);
                varTimesPoly 3 (eval3t 2 t2) ]
  | 2, Node(t1, t2) -> 
      addPoly [ varTimesPoly 4 (eval3t 2 t1); 
                varTimesPoly 5 (eval3t 2 t2);
                varTimesPoly 6 (eval3t 3 t1); 
                varTimesPoly 7 (eval3t 3 t2) ]
  | 3, Node(t1, t2) -> 
      addPoly [ varTimesPoly 8 (eval3t 3 t1); 
                varTimesPoly 9 (eval3t 3 t2);
                varTimesPoly 10 (eval3t 1 t1); 
                varTimesPoly 11 (eval3t 1 t2) ]
  | _ -> E.s (bug "eval2m")

let treeDepth = ref 8

let test_poly () = 
  ignore (E.log "Here I am playing with polynomials\n");
  let rec mkBalanced (path: string) (depth: int) = 
    if depth = 0 then 
      Leaf path
    else
      Node (mkBalanced (path ^ "L") (depth - 1),
            mkBalanced (path ^ "R") (depth - 1))
  in
  let t = mkBalanced "" !treeDepth in
  let p = eval3t 1 t in
  printPolyByMonomial p;
  solve p;
  ()

let doit (f: file) = 
  let rec doOneFunction (fi: fundec) = 
    ignore (E.log "RAND: doing function %s\n" fi.svar.vname);
    (* Let's do a topological sort of the statements. We scan statements and 
     * we remember those that we have done. We also keep a todo list. These 
     * are statements that are waiting on some predecessor to be done *)
    let root: stmt option = 
      match fi.sbody.bstmts with 
        [] -> (* Empty function *) None
      | f :: _ -> Some f
    in
    let todo: stmt list ref = 
      ref (match root with None -> [] | Some r -> [r]) in
    let doneStmts : (int, unit) H.t = H.create 13 in
    let doOneStatement (s: stmt) = 
      if H.mem doneStmts s.sid then () else begin
        ignore (E.log " %d," s.sid);
        H.add doneStmts s.sid ();
        (* Now add all successors to the todo list *)
        todo := s.succs @ !todo 
      end
    in
    let rec loop () = 
      match !todo with 
        [] -> (* We are done *) ()
      | n :: rest -> 
          (* Pick one that has all the predecessors done *)
          let ready, notready = 
            List.partition
              (fun n -> 
                H.mem doneStmts n.sid || 
                List.for_all (fun p -> H.mem doneStmts p.sid) n.preds)
              !todo
          in
          (* See if there are no ready statements *)
          if ready = [] then begin
            (* Break a cycle on the first element in todo *)
            ignore (E.log "(*)");
            todo := rest;
            doOneStatement n;
            loop ();
          end else begin
            todo := notready; (* notready is shorter now *)
            (* Do all the ready ones *)
            List.iter doOneStatement ready;
            loop ()
          end
    
    in 
    Stats.time "rand" loop ();
    ignore (E.log "\n");
  in
  List.iter 
    (fun g -> 
      match g with 
        GFun (fi, _) -> doOneFunction fi
      | _ -> ())
    f.globals


let feature : featureDescr = 
  { fd_name = "rand";
    fd_enabled = enabled;
    fd_description = "randomized global value numbering";
    fd_extraopt = [
      ("--rand-test-poly", Arg.Unit test_poly, 
        "do some testing with polynomials");
      ("--rand-test-depth", Arg.Int (fun n -> treeDepth := n), 
        "the depth of the tree")
    ];
    fd_doit = doit;
    fd_post_check = false; (* No changes to the file *)
}

