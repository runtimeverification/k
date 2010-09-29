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

module F = Frontc
module C = Cil
module CK = Check
module E = Errormsg
open Printf
open CabsPrinter

(* let printerForCabs = new cabsPrinter*) 

type outfile = 
    { fname: string;
      fchan: out_channel } 
let outChannel : outfile option ref = ref None
let mergedChannel : outfile option ref = ref None


let replace input output =
    Str.global_replace (Str.regexp_string input) output
	
let noscores s = 
	(replace "_" "u" s)

let fileContents : string ref = ref ""

let parseOneFile (fname: string) =
  (* PARSE *)
  if !Cilutil.printStages then ignore (E.log "Parsing %s\n" fname);
  (*let cil = F.parse fname () in *)
  let cabs = fst(F.parse_with_cabs fname ()) in
  cabs
  
  
let rec processOneFile (cabs: Cabs.file) =
	fileContents := "";
  begin
    (match !outChannel with
      None -> ()
    | Some c -> (
		let (inputFilename, _) = cabs in
		let ic = open_in inputFilename in (
		try
			while true do
				let line = input_line ic in  (* read line from in_channel and discard \n *)
				if (String.length line < 5 or Str.first_chars line 5 <> "# 1 \"") then
					fileContents := (!fileContents ^ line ^ "\n");
			done
		with e ->                      (* some unexpected exception occurs *)
			close_in_noerr ic;           (* emergency closing *)
		);
		let programName = 
		Filename.basename (replace "-gen-maude-tmp" "" (replace "." "-" ("program-" ^ (noscores c.fname)))) in
			fprintf c.fchan "%s\n" ("op " ^ programName ^ " : -> Program .");
			let maude = (cabsToString cabs !fileContents) in
				(fprintf c.fchan "eq %s = (%s) .\n" programName maude); 
	));

    if !E.hadErrors then
      E.s (E.error "Error while processing file; see above for details.");

  end
        
(***** MAIN *****)  
let theMain () =
  let usageMsg = "Usage: cilly [options] source-files" in
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
  (* sm: enabling this by default, since I think usually we
   * want 'cilly' transformations to preserve annotations; I
   * can easily add a command-line flag if someone sometimes
   * wants these suppressed *)
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
        @ F.args in
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
      let files = Util.list_map parseOneFile !Ciloptions.fileNames in

      (* if there's more than one source file, merge them together; *)
      (* now we have just one CIL "file" to deal with *)
      let one =
        match files with
          [one] -> one
        | [] -> E.s (E.error "No arguments for CIL")
        | _ -> E.s (E.error "Can only handle one input file")
            (* let merged =
              Stats.time "merge" (Mergecil.merge files)
                (if !outName = "" then "stdout" else !outName) in
            if !E.hadErrors then
              E.s (E.error "There were errors during merging");
            (* See if we must save the merged file *)
            (match !mergedChannel with
              None -> ()
            | Some mc -> begin
                let oldpci = !C.print_CIL_Input in
                C.print_CIL_Input := true;
                Stats.time "printMerged"
                  (C.dumpFile !C.printerForMaincil mc.fchan mc.fname) merged;
                C.print_CIL_Input := oldpci
            end);
            merged *)
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

