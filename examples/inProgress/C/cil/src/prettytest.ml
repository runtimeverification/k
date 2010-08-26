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

open Pretty;;
(*
let a = Pretty.dprintf "Aman"
let b = Pretty.dprintf "%d" 3
let c = (Pretty.dprintf "%d%a" 4 (fun a b -> b)  a)


let rec deepDoc depth =
  if (depth == 0) then (Pretty.dprintf "")
  else begin (Pretty.dprintf 
	  "@[Aman?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?@?%d @? %a @?@]" 
	  depth 
	  (fun a b -> b) 
	  (deepDoc (depth - 1))) end

let dotest () =
  Pretty.noBreaks := false;
  Pretty.noAligns := false;
  for i=1 to 50 do
    Pretty.fprint stdout 20 (deepDoc 50)
  done;;
*)
(* dotest ()*)

let strings = [| "some" ; "dummy" ; "strings" ; "that" ; "are" ; "statically" ; "allocated" ; "." |]

type stringTree = TNode of stringTree * stringTree   | TLeaf of string 

let rec makeStringTree (levels : int) : stringTree =
  if levels = 0 then TLeaf strings.(Random.int (Array.length strings))
  else TNode (makeStringTree (levels - Random.int 2) , 
	      makeStringTree (levels - 1))


let rec boo  = function
    TLeaf s -> 1
  | TNode (a,b) -> (boo a) + (boo b)

let rec treeMap leafFun nodeFun = function 
    TLeaf s -> leafFun s
  | TNode (a,b) -> nodeFun (treeMap leafFun nodeFun a) (treeMap leafFun nodeFun  b)

let countLeaves = treeMap (function _ -> 1) (+)

let tree2doc = (treeMap 
		   (fun s -> dprintf "%s" s)
		   (fun d1 d2 -> dprintf "(@[%a@?+@?%a@])" insert d1 insert d2))

let treeTest n colWidth =
  
  Pretty.noBreaks := false;
  Pretty.noAligns := false;
  Random.init 10;

  ignore (Pretty.fprintf stderr "prettytest: Depth = %d " n);
  ignore (flush stderr);
  let mode = try Sys.getenv "MODE" with Not_found -> "" in
  let t = makeStringTree n in 
  ignore (Printf.fprintf stderr "Mode = %s Tree size = %d \t ColWidth = %d\n" mode (countLeaves t) colWidth);
  ignore (flush stderr);
  if mode <> "SkipPrint" then 
    let start = Sys.time () in
    Pretty.fprint stdout colWidth (tree2doc t);
    let finish = Sys.time () in
    Printf.fprintf stderr"Print time: %f\n" (finish -. start)
	

let doTest () =
  let width = try (int_of_string (Sys.getenv "WIDTH")) with Not_found -> 80 in
  let depth = try (int_of_string (Sys.getenv "DEPTH")) with Not_found -> 9 in
  let marshalFilename = 
    try Sys.getenv "MARSHALREAD"       
    with Not_found -> (treeTest depth width) ; exit 0
  in
  Printf.fprintf stderr "Marshalling in %s\n" marshalFilename;
  let chn = open_in_bin marshalFilename in
  let fcount = ref 0 in
  try
    while true do
      Pretty.fprint stdout width (Obj.magic (Marshal.from_channel chn) : doc);
      fcount := !fcount + 1
    done
  with End_of_file -> begin
    Printf.fprintf stderr "%d documents printed from marshaled file\n" !fcount;
    ()
  end
;;

doTest ();;

