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
 



(* main.ml *)
(* this module is the program entry point for the 'cilly' program, *)
(* which reads a C program file, parses it, translates it to the CIL *)
(* intermediate language, and then renders that back into C *)
open Cil
open MaudeVisitor
open MaudePrinter
open Escape
open Pretty

module F = Frontc
module C = Cil
module CK = Check
module E = Errormsg
module H = Hashtbl


let printerForMaincil = new maudePrinter
(* new maudePrinter *)
(* new plainCilPrinterClass *)
(* new defaultCilPrinterClass *)
(* ((new descriptiveCilPrinterClass true) :> descriptiveCilPrinter) *)


let strcontains s1 s2 =
try 
	(Str.search_forward (Str.regexp_string s2) s1 0);
	true
with
| e -> false

let replace input output =
    Str.global_replace (Str.regexp_string input) output
	
let noscores s = 
	(replace "_" "u" s)
	
(* variables to help generate maude.  These get set by calling the maude visitor *)
let identifierList : string list ref = ref []
let typedefList : string list ref = ref []

(* for removing duplicates *)
let add_elem elem list = if List.mem elem list then list else elem :: list
let nub list = List.fold_right add_elem list []

(* let maudeHeader = "(fmod C-PROGRAMS is including C-SYNTAX .\n"
let maudeFooter = "endm)" *)
let maudeHeader = ""
let maudeFooter = ""
  
let defineConstant name sort = ("op " ^ (noscores name) ^ " : -> " ^ sort ^ " [ctor] .\n")
let printString out x = fprintf out "%s" x

type outfile = 
    { fname: string;
      fchan: out_channel } 
let outChannel : outfile option ref = ref None
let mergedChannel : outfile option ref = ref None

let parseOneFile (fname: string) : C.file =
  (* PARSE and convert to CIL *)
  if !Cilutil.printStages then ignore (E.log "Parsing %s\n" fname);
  let cil = F.parse fname () in
  
  if (not !Epicenter.doEpicenter) then (
    (* sm: remove unused temps to cut down on gcc warnings  *)
    (* (Stats.time "usedVar" Rmtmps.removeUnusedTemps cil);  *)
    (* (trace "sm" (dprintf "removing unused temporaries\n")); *)
    (Rmtmps.removeUnusedTemps cil)
  );
  cil

let rec printIdentifierList (out : out_channel) (l : string list) = match l with 
	| x :: xs -> 
		(if (x = "main" || strcontains x "fslAnnotation") then text "" else (printString out (defineConstant x "Id")));
		printIdentifierList out xs
	| [] -> ()
	
let rec printTypedefList (out : out_channel) (l : string list) = match l with 
	| x :: xs -> 
		(*printString out (defineConstant x "Typedef-Name");*)
		printString out (defineConstant x "Id");
		printTypedefList out xs
	| [] -> ()	
	
let printNewline (out : out_channel) = fprintf out "%s\n" ""

let rec parenRight f xs = 
	match xs with
		| x::xs -> paren(paren(f x) ++ (parenRight f xs))
		| [] -> nil
		
let myIterGlobals (fl: file) doone =
  let doone' g = 
      currentLoc := get_globalLoc g;
      doone g
  in
  parenRight doone' fl.globals
  (*(match fl.globinit with
    None -> nil
  | Some g -> doone' (GFun(g, locUnknown))) *)
  
let myDumpFile (pp: cilPrinter) (out : out_channel) (outfile: string) file =
  printDepth := 99999;  (* We don't want ... in the output *)
  (* If we are in RELEASE mode then we do not print indentation *)

  Pretty.fastMode := true;

  if !E.verboseFlag then
    ignore (E.log "printing file %s\n" outfile);

	(*fprintf out "%s\n" "(mod GEN-C-PROGRAM is including C-SYNTAX ."; *)
	printIdentifierList out !identifierList;
	printNewline out;
	printTypedefList out !typedefList;
	printNewline out;
	fprintf out "------------END-OPERATORS------------\n";
	
	let programName = 
		Filename.basename (replace "-gen-maude-tmp" "" (replace "." "-" ("program-" ^ (noscores outfile)))) in
			fprintf out "%s\n" ("op " ^ programName ^ " : -> Program .");
			fprintf out "%s\n" ("eq " ^ programName ^ " = ("); 
	
	
	(*fprintf out "%s\n" (List.hd !identifierList);*)
	let print x = fprint out 78 x in
	(*print (text ("/* Generated by CIL v. " ^ cilVersion ^ " */\n" ^
			   (* sm: I want to easily tell whether the generated output is with print_CIL_Input or not *)
			   "/* print_CIL_Input is " ^ (if !print_CIL_Input then "true" else "false") ^ " */\n\n"));*)
	fprintf out "%s" (sprint 10000 (myIterGlobals file (fun g -> printGlobal pp () g)));
	
	
	fprintf out "%s\n" ") .";
	(* fprintf out "%s\n" "endm)"; *)
	(* sm: we have to flush the output channel; if we don't then under *)
	(* some circumstances (I haven't figure out exactly when, but it happens *)
	(* more often with big inputs), we get a truncated output file *)
	flush out

let rec processOneFile (cil: C.file) =
  begin
	  (* Run the feature, and see how long it takes. *)
	  (function (f: file) -> 
		  let visitor = new maudeVisitor in
		  visitCilFileSameGlobals (visitor :> Cil.cilVisitor) f; 
		  identifierList := nub (visitor#getIdentifierList) ;
		  typedefList := nub (visitor#getTypedefList) ;
		  ) cil;

    (match !outChannel with
      None -> ()
    | Some c -> Stats.time "printCIL" 
	(myDumpFile (printerForMaincil :> Cil.cilPrinter) c.fchan c.fname) cil);

    if !E.hadErrors then
      E.s (E.error "Error while processing file; see above for details.");

  end
        
(***** MAIN *****)  
let theMain () =
  let usageMsg = "Usage: " ^ Sys.argv.(0) ^ " [options] source-files" in
  (* Processign of output file arguments *)
  let openFile (what: string) (takeit: outfile -> unit) (fl: string) = 
    if !E.verboseFlag then
      ignore (Printf.printf "Setting %s to %s\n" what fl);
    (try takeit { fname = fl;
                  fchan = open_out fl }
    with _ ->
      raise (Arg.Bad ("Cannot open " ^ what ^ " file " ^ fl)))
  in
  let outName = ref "" in
  C.print_CIL_Input := true;

  (*********** COMMAND LINE ARGUMENTS *****************)
  (* Construct the arguments for the features configured from the Makefile *)
  let blankLine = ("", Arg.Unit (fun _ -> ()), "") in
    
  let argDescr = Ciloptions.options @ 
        [ 
          "--out", Arg.String (openFile "output" 
                                 (fun oc -> outChannel := Some oc)),
              " the name of the output CIL file.\n\t\t\t\tThe cilly script sets this for you.";
          "--mergedout", Arg.String (openFile "merged output"
                                       (fun oc -> mergedChannel := Some oc)),
              " specify the name of the merged file";
        ]
        in
  begin
    (* this point in the code is the program entry point *)

    Stats.reset Stats.HardwareIfAvail;

    (* parse the command-line arguments *)
    Arg.parse (Arg.align argDescr) Ciloptions.recordFile usageMsg;
    Cil.initCIL ();

    Ciloptions.fileNames := List.rev !Ciloptions.fileNames;

    if !Cilutil.testcil <> "" then begin
      Testcil.doit !Cilutil.testcil
    end else
      (* parse each of the files named on the command line, to CIL *)
      let files = List.map parseOneFile !Ciloptions.fileNames in

      (* if there's more than one source file, merge them together; *)
      (* now we have just one CIL "file" to deal with *)
      let one =
        match files with
          [one] -> one
        | [] -> E.s (E.error "No arguments for CIL")
      in

      if !E.hadErrors then
        E.s (E.error "Cabs2cil had some errors");

      (* process the CIL file (merged if necessary) *)
      processOneFile one
  end
;;
                                        (* Define a wrapper for main to 
                                         * intercept the exit *)
let failed = ref false 

let cleanup () = 
  if !E.verboseFlag || !Cilutil.printStats then
    Stats.print stderr "Timings:\n";
  if !E.logChannel != stderr then 
    close_out (! E.logChannel);  
  (match ! outChannel with Some c -> close_out c.fchan | _ -> ())


(* Without this handler, cilly.asm.exe will quit silently with return code 0
   when a segfault happens. *)
let handleSEGV code =
  if !Cil.currentLoc == Cil.locUnknown then
    E.log  "**** Segmentation fault (possibly a stack overflow)\n"
  else begin
    E.log ("**** Segmentation fault (possibly a stack overflow) "^^
           "while processing %a\n")
      Cil.d_loc !Cil.currentLoc
  end;
  exit code

let _ = Sys.set_signal Sys.sigsegv (Sys.Signal_handle handleSEGV);

;;

begin 
  try 
    theMain (); 
  with F.CabsOnly -> (* this is OK *) ()
end;
cleanup ();
exit (if !failed then 1 else 0)

