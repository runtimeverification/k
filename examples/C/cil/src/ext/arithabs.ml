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
module E = Errormsg
module CG = Callgraph
module H = Hashtbl 
module U = Util
module IH = Inthash
module VS = Usedef.VS

module S = Ssa

let debug = false
let prologue = "["
let epilogue = "]"

let arithAbsOut = ref stdout
let setArithAbsFile (s: string) =
  try 
    arithAbsOut := open_out s
  with _ -> ignore (E.warn "Cannot open the output file %s" s)

(* Print out *)
let pd ?(ind=0) (d: doc) : unit = 
  Pretty.fprint !arithAbsOut 80 (indent ind d)

let p ?(ind=0) (fmt : ('a,unit,doc) format) : 'a = 
  let f d =  
    pd ~ind:ind d;
    nil 
  in
  Pretty.gprintf f fmt


(** Variables whose address is taken are ignores. Set this to true if you 
 * want references to the address of such variables to be printed as the only 
 * accesses of the variable *)
let treatAddressOfAsRead = true

(** The globals written, indexed by Id of the function variable. Each inner 
 * table is indexed by the global id *)
let globalsWritten: (varinfo IH.t) IH.t = IH.create 13
let currentGlobalsWritten: (varinfo IH.t) ref = ref (IH.create 13)


(** The transitive closure of the globals written *)
let globalsWrittenTransitive: (varinfo IH.t) IH.t = IH.create 13

let globalsRead: (varinfo IH.t) IH.t = IH.create 13
let currentGlobalsRead: (varinfo IH.t) ref = ref (IH.create 13)

let globalsReadTransitive: (varinfo IH.t) IH.t = IH.create 13


let getGlobalsWrittenTransitive (f: varinfo): varinfo list = 
  try
    let glob_written_trans = 
      IH.find globalsWrittenTransitive f.vid 
    in
    IH.fold
      (fun _ g acc -> g :: acc)
      glob_written_trans
      []
  with Not_found -> [] (* not a defined function *)

let getGlobalsReadTransitive (f: varinfo) = 
  try
    let glob_read_trans = 
      IH.find globalsReadTransitive f.vid 
    in
    IH.fold
      (fun _ g acc -> g :: acc)
      glob_read_trans
      []
  with Not_found -> []
  
let considerType (t: typ) : bool = 
  (* Only consider those types for this we can do arithmetic *)
  (match unrollType t with 
    TInt _ | TEnum _ | TPtr _ | TFloat _ -> true
  | _ -> false)

let considerVariable (v: varinfo) : bool = 
  not v.vaddrof && considerType v.vtype

class gwVisitorClass : cilVisitor = object (self) 
  inherit nopCilVisitor

  method vexpr = function
      Lval (Var v, _) when v.vglob && considerVariable v -> 
        IH.replace !currentGlobalsRead v.vid v;
        DoChildren

      (* We pretend that when we see the address of a global, we are reading 
       * from the variable. Note that these variables will not be among those 
       * that we "considerVariable" so, there will be no writing to them *)
    | StartOf (Var v, NoOffset) 
    | AddrOf (Var v, NoOffset) when treatAddressOfAsRead && v.vglob -> 
        IH.replace !currentGlobalsRead v.vid v;
        DoChildren 

    | _ -> DoChildren

  method vinst = function
      Set ((Var v, _), _, _) 
    | Call (Some (Var v, _), _, _, _) when v.vglob && considerVariable v -> 
        IH.replace !currentGlobalsWritten v.vid v;
        (* When we write a global, we also consider that we are reading it. 
         * This is useful if the global is not written on all paths *)
        IH.replace !currentGlobalsRead v.vid v; 
        DoChildren
    | _ -> DoChildren
end

let gwVisitor = new gwVisitorClass


(** Functions can be defined or just declared *)
type funinfo = 
    Decl of varinfo
  | Def of fundec

(* All functions indexed by the variable ID *)
let allFunctions: funinfo IH.t = IH.create 13


(** Compute the SSA form *)
 


    
let fundecToCFGInfo (fdec: fundec) : S.cfgInfo = 
  (* Go over the statments and make sure they are numbered properly *)
  let count = ref 0 in
  List.iter (fun s -> s.sid <- !count; incr count) fdec.sallstmts;

  let start: stmt = 
    match fdec.sbody.bstmts with
      [] -> E.s (E.bug "Function %s with no body" fdec.svar.vname)
    | fst :: _ -> fst
  in
  if start.sid <> 0 then 
    E.s (E.bug "The first block must have index 0");
  
  
  let ci = 
    { S.name  = fdec.svar.vname;
      S.start = start.sid;
      S.size  = !count;
      S.successors = Array.make !count [];
      S.predecessors = Array.make !count [];
      S.blocks = Array.make !count { S.bstmt = start; 
                                     S.instrlist = [];
                                     S.reachable = true;
                                     S.livevars = [] };
      S.nrRegs = 0;
      S.regToVarinfo = Array.make 0 dummyFunDec.svar;
    } 
  in

  (* Map a variable to a register *)
  let varToRegMap: S.reg IH.t = IH.create 13 in 
  let regToVarMap: varinfo IH.t = IH.create 13 in 
  let varToReg (v: varinfo) : S.reg = 
    try IH.find varToRegMap v.vid
    with Not_found -> 
      let res = ci.S.nrRegs in 
      ci.S.nrRegs <- 1 + ci.S.nrRegs;
      IH.add varToRegMap v.vid res;
      IH.add regToVarMap res v;
      res
  in
  (* For functions, we use the transitively computed set of globals and 
   * locals as the use/def *)
  Usedef.getUseDefFunctionRef := 
    (fun f args ->
      match f with 
        Lval (Var fv, NoOffset) -> 
          let varDefs = ref VS.empty in 
          let varUsed = ref VS.empty in 
          (try 
            let gw = IH.find globalsWrittenTransitive fv.vid in
            IH.iter 
              (fun _ g -> varDefs := VS.add g !varDefs) gw
          with Not_found -> (* Do not have a definition for it *)
            ());
          (* Now look for globals read *)
          (try 
            let gr = IH.find globalsReadTransitive fv.vid in 
            IH.iter
              (fun _ g -> varUsed := VS.add g !varUsed) gr
          with Not_found -> ());

          !varUsed, !varDefs, args

      | _ -> VS.empty, VS.empty, args);


  Usedef.considerVariableUse := 
    (fun v -> considerVariable v);
  Usedef.considerVariableDef := 
    (fun v -> considerVariable v);
  Usedef.considerVariableAddrOfAsUse := 
    (fun v -> treatAddressOfAsRead);

  (* Filter out the variables we do not care about *)
  let vsToRegList (vs: VS.t) : int list = 
    VS.fold (fun v acc -> (varToReg v) :: acc) vs [] 
  in
  List.iter 
    (fun s -> 
      ci.S.successors.(s.sid) <- Util.list_map (fun s' -> s'.sid) s.succs;
      ci.S.predecessors.(s.sid) <- Util.list_map (fun s' -> s'.sid) s.preds;
      ci.S.blocks.(s.sid) <- begin
        let instrs: (S.reg list * S.reg list) list = 
          match s.skind with 
            Instr il -> 
              (* Each instruction is transformed independently *)
              Util.list_map (fun i -> 
                let vused, vdefs = Usedef.computeUseDefInstr i in 
                (vsToRegList vdefs, vsToRegList vused)) il
                
          | Return (Some e, _) 
          | If (e, _, _, _) 
          | Switch (e, _, _, _) ->
              let vused = Usedef.computeUseExp e in 
              [ ([], vsToRegList vused) ]
                
          | Break _ | Continue _ | Goto _ | Block _ | Loop _ | Return _ -> [ ]
          | TryExcept _ | TryFinally _ -> assert false
        in
        { S.bstmt = s;
          S.instrlist = instrs;
          S.livevars = []; (* Will be filled in later *)
          S.reachable = true; (* Will be set later *)
        }
      end
    ) fdec.sallstmts;

  (* Set the mapping from registers to variables *)
  ci.S.regToVarinfo <-
    Array.make ci.S.nrRegs dummyFunDec.svar;
  IH.iter (fun rid v -> 
    ci.S.regToVarinfo.(rid) <- v) regToVarMap;

  ci

(* Compute strongly-connected components *)
let stronglyConnectedComponents (cfg: S.cfgInfo) : bool -> S.sccInfo = 
  S.stronglyConnectedComponents cfg 


let globalsDumped = IH.create 13


(** We print variable names in a special way *)
let variableName (v: varinfo) (freshId: int) = 
  (if v.vaddrof then begin          
     assert treatAddressOfAsRead;
     "addrof_"
   end else "") ^ 
  (if v.vglob then "glob_" else "") ^
  (if freshId = 0 then 
    v.vname
  else
    v.vname ^ "___" ^ string_of_int freshId) 
  
(** Use a hash table indexed by varinfo *)
module VH = Hashtbl.Make(struct 
                           type t = varinfo 
                           let hash (v: varinfo) = v.vid
                           let equal v1 v2 = v1.vid = v2.vid
                         end)

let vhToList (vh: 'a VH.t) : (varinfo * 'a) list = 
  VH.fold (fun v id acc -> (v, id) :: acc) vh []

let debugRename = false

(** We define a new printer *)
class absPrinterClass (callgraph: CG.callgraph) : cilPrinter = 

  let lastFreshId= ref 0 in 

  (* freshVarId returns at least 1 *)
  let freshVarId () = incr lastFreshId; !lastFreshId in
  

  object (self) 
    inherit defaultCilPrinterClass as super
        
    val mutable idomData: stmt option IH.t = IH.create 13

    val mutable cfgInfo: S.cfgInfo option = None 
        

    val mutable sccInfo: S.sccInfo option = None

    val mutable currentFundec = dummyFunDec

        (** For each block end, a mapping from IDs of variables to their ID 
         * at the end of the block *)
    val mutable blockEndData: int VH.t array = 
      Array.make 0 (VH.create 13)

        (** For each block start, remember the starting newFreshId as we 
         * start the block *)
    val mutable blockStartData: int array = 
      Array.make 0 (-1) 


    val mutable varRenameState: int VH.t = VH.create 13

          (* All the fresh variables *)
    val mutable freshVars: string list = []

          (* The uninitialized variables are those that are live on input but 
           * not globals or formals. *)
    val mutable uninitVars: string list = []

    method private initVarRenameState (b: S.cfgBlock) =
      VH.clear varRenameState;
      
      let cfgi = 
        match cfgInfo with
          None -> assert false
        | Some cfgi -> cfgi
      in
        
      (* Initialize it based on the livevars info in the block *)
      List.iter 
        (fun (rid, defblk) -> 
          let v = cfgi.S.regToVarinfo.(rid) in
          if defblk = b.S.bstmt.sid then
            (* Is a phi variable or a live variable at start *)
            if defblk = cfgi.S.start then begin
              (* For the start block, use ID=0 for all variables, except the 
               * locals that are not function formals. Those are fresh 
               * variables. *)
              let isUninitializedLocal = 
                not v.vglob &&
                (not (List.exists (fun v' -> v'.vid = v.vid) 
                        currentFundec.sformals)) in
              VH.add varRenameState v 0;
              let vn = self#variableUse varRenameState v in
              if isUninitializedLocal then 
                uninitVars <- vn :: uninitVars;
            end else begin
              VH.add varRenameState v (freshVarId ());
              let vn = self#variableUse varRenameState v in
              freshVars <- vn :: freshVars
            end
          else begin 
            let fid = 
              try VH.find blockEndData.(defblk) v
              with Not_found -> 
                E.s (E.bug "In block %d: Cannot find data for variable %s in block %d"
                       b.S.bstmt.sid v.vname defblk)
            in
            VH.add varRenameState v fid
          end)
        b.S.livevars;
      
      if debugRename then 
        ignore (E.log "At start of block %d:\n   @[%a@]\n"
                  b.S.bstmt.sid
                  (docList ~sep:line
                     (fun (v, id) -> 
                       dprintf "%s: %d" v.vname id))
                  (vhToList varRenameState));
      ()
    
    (** This is called for reading from a variable we consider (meaning that 
     * its address is not taken and has the right type) *)
    method private variableUse ?(print=true) 
                               (state: int VH.t) (v: varinfo) : string = 
      let freshId = 
        try VH.find state v
        with Not_found -> 
          E.s (E.bug "%a: varUse: varRenameState does not know anything about %s" 
                 d_loc !currentLoc v.vname )
      in
      if debugRename && print then 
        ignore (E.log "At %a: variableUse(%s) : %d\n" 
                  d_loc !currentLoc v.vname freshId);
      variableName v freshId
        
    method private variableDef (state: int VH.t) (v: varinfo) : string = 
      assert (not v.vaddrof);
      let newid = freshVarId () in 
      VH.replace state v newid;
      if debugRename then 
        ignore (E.log "At %a: variableDef(%s) : %d\n" 
                  d_loc !currentLoc v.vname newid);
      let n = self#variableUse ~print:false state v in
      freshVars <- n :: freshVars;
      n
    
    method pExp () = function
      | Const (CInt64(i, _, _)) -> text (Int64.to_string i)
      | Const (CStr _) -> text "(@rand)"
      | BinOp (bop, e1, e2, _) -> 
          dprintf "(%a @[%a@?%a@])" 
            d_binop bop
            self#pExp e1 self#pExp e2
      | UnOp (uop, e1, _) -> 
          dprintf "(%a @[%a@])"
            d_unop uop self#pExp e1
      | CastE (t, e) -> self#pExp () e (* Ignore casts *)
            
      | Lval (Var v, NoOffset) when considerVariable v -> 
          text (self#variableUse varRenameState v)
            
            (* We ignore all other Lval *)
      | Lval _ -> text "(@rand)" 


      | AddrOf (Var v, NoOffset) 
      | StartOf (Var v, NoOffset) -> 
          if treatAddressOfAsRead then 
            text (self#variableUse varRenameState v)
          else
            text "(@rand)"


      | e -> super#pExp () e
            
    method pInstr () (i: instr) = 
      (* Print a call *)
      let printCall (dest: varinfo option) 
                    (f: varinfo) (args: exp list) (l: location) = 
        currentLoc := l;
        let gwt: varinfo list = getGlobalsWrittenTransitive f in
        let grt: varinfo list = getGlobalsReadTransitive f in

        let gwt' = 
          match dest with 
            Some dest -> gwt @ [dest] 
          | _ -> gwt 

        in 
        (* Prepare the arguments first *)
        let argdoc: doc = 
          (docList ~sep:break (self#pExp ())) 
            ()
            (args @ (Util.list_map (fun v -> Lval (Var v, NoOffset)) grt))
        in 
        dprintf "%a = (%s @[%a@]);"
          (docList 
             (fun v -> 
               text (self#variableDef varRenameState v)))
          gwt'
          f.vname
          insert argdoc
      in     
      match i with 
      | Set ((Var v, NoOffset), e, l) when considerVariable v -> 
          currentLoc := l;
          (* We must do the use first *)
          let use = self#pExp () e in 
          text (self#variableDef varRenameState v) 
            ++ text "=" ++ use ++ text ";"
            
      | Call (Some (Var v, NoOffset), 
              Lval (Var f, NoOffset), args, l) when considerVariable v ->
          printCall (Some v)
                    f args l      

       (* Ignore the result if not a variable we are considering *)
      | Call (_, Lval (Var f, NoOffset), args, l) -> 
          printCall None f args l
            

      | _ -> nil (* Ignore the other instructions *)        
            

    method dBlock (out: out_channel) (ind: int) (b: block) : unit = 
      ignore (p ~ind:ind "%sblock\n" prologue);
      List.iter (self#dStmt out (ind+ 2)) b.bstmts;
      ignore (p ~ind:ind "%s\n" epilogue)
        
    method dStmt (out: out_channel) (ind: int) (s: stmt) : unit = 
      currentLoc := get_stmtLoc s.skind;
      (* Initialize the renamer for this statement *)
      lastFreshId := blockStartData.(s.sid);
      if debugRename then 
        ignore (E.log "Initialize the renamer for block %d to %d\n" 
                  s.sid !lastFreshId);
      assert (!lastFreshId >= 0);

      let cfgi = 
        match cfgInfo with
          Some cfgi -> cfgi
        | None -> assert false
      in
      let blk: S.cfgBlock = cfgi.S.blocks.(s.sid) in 
      assert (blk.S.bstmt == s);
        
      self#initVarRenameState blk;

      let phivars: varinfo list = 
        List.fold_left
          (fun acc (i, defblk) -> 
            if defblk = s.sid then 
              cfgi.S.regToVarinfo.(i) :: acc
            else 
              acc)
          []
          blk.S.livevars 
      in
      (* do not emit phi for start block *)
      let phivars: varinfo list = 
        if s.sid = cfgi.S.start then 
          []
        else
          phivars
      in

      (* Get the predecessors information *)
      let getPhiAssignment (v: varinfo) : (string * string list) = 
        (* initVarRenameState has already set the state for the phi register *)
        let lhs: string = self#variableUse varRenameState v in 
        let rhs: string list = 
          Util.list_map
            (fun p -> 
              self#variableUse blockEndData.(p) v)
            cfgi.S.predecessors.(s.sid)
        in
        (lhs, rhs)
      in

      pd (self#pLineDirective (get_stmtLoc s.skind));
      (* Lookup its dominator *)
      let idom: doc = 
        match Dominators.getIdom idomData s with 
          Some dom -> num dom.sid
        | None -> nil
      in

      let headerstuff = 
        (* See if this block is a header *)
        let scc = 
          match sccInfo with Some x -> x 
          | _ -> E.s (E.bug "sccInfo is not set")
        in
        if List.exists (fun sci -> List.mem s.sid sci.S.headers) scc then begin
          (* We get the variables at the end of any predecessor. *)
          let p: int = 
            match cfgi.S.predecessors.(s.sid) with 
              p :: _ -> p
            | [] -> E.s (E.bug "Header block %d has no predecessors" s.sid)
          in
          let pend: int VH.t = blockEndData.(p) in
          let allvars: (varinfo * int) list = vhToList pend in 

          let nonphi: (varinfo * int) list = 
            List.filter 
              (fun (v, _) -> 
                not (List.exists (fun v' -> v'.vid = v.vid) phivars)) allvars
          in
            
          dprintf "%snonphi %a%s\n"
            prologue 
            (docList 
               (fun (v, vvariant) -> 
                 text (variableName v vvariant)))
            nonphi
            epilogue
        end else
          nil
      in
        
      let succs = List.filter (fun s' -> cfgi.S.blocks.(s'.sid).S.reachable) s.succs in
      let preds = List.filter (fun s' -> cfgi.S.blocks.(s'.sid).S.reachable) s.preds in
      ignore (p ~ind:ind
                "%sstmt %d %a %ssuccs %a%s %spreds %a%s %sidom %a%s\n  @[%a@]\n"
                prologue s.sid (** Statement id *)
                insert headerstuff
                prologue (d_list "," (fun _ s' -> num s'.sid)) succs epilogue
                prologue (d_list "," (fun _ s' -> num s'.sid)) preds epilogue
                prologue insert idom epilogue
                (docList ~sep:line 
                   (fun pv -> 
                     let (lhs, rhs) = getPhiAssignment pv in 
                     dprintf "%s = (@@phi %a);" 
                       lhs (docList ~sep:break text) rhs))
                phivars
                );
      (* Now the statement kind *)
      let ind = ind + 2 in 
      (match s.skind with 
      | Instr il -> 
          if (cfgi.S.blocks.(s.sid).S.reachable) then begin
	    List.iter 
              (fun i -> 
              pd ~ind:ind (self#pInstr () i ++ line))
              il
	  end
      | Block b -> List.iter (self#dStmt out ind) b.bstmts
      | Goto (s, _) -> ignore (p ~ind:ind "%sgoto %d%s\n" prologue !s.sid epilogue)
      | Return (what, _) -> begin

          let gwt: varinfo list = 
            getGlobalsWrittenTransitive currentFundec.svar
          in
          let res: varinfo list = 
            match what with 
              None -> gwt
            | Some (Lval (Var v, NoOffset)) when v.vname = "__retres" -> 
                if considerType v.vtype then 
                  gwt @ [ v ]
                else
                  gwt
            | Some e -> 
                E.s (E.bug "Return with no __retres: %a" d_exp e)
          in
          ignore (p ~ind:ind
                    "return %a;"
                    (docList 
                       (fun v -> 
                         text (self#variableUse varRenameState v)))
                 res);
      end

      | If(e, b1, b2, _) -> 
          ignore (p ~ind:ind "%sif %a\n" prologue self#pExp e);
          self#dBlock out (ind + 2) b1;
          self#dBlock out (ind + 2) b2;
          ignore (p ~ind:ind "%s\n" epilogue)
            
      | Loop (b, _, Some co, Some br) -> 
          ignore (p ~ind:ind "%sloop %scont %d%s %sbreak %d%s\n" 
		    prologue 
		    prologue co.sid epilogue 
		    prologue br.sid epilogue);
          List.iter (self#dStmt out (ind+ 2)) b.bstmts;
          ignore (p ~ind:ind "%s\n" epilogue)
            
            (* The other cases should have been removed already *)
      | _ -> E.s (E.unimp "try except"));
      
      (* The termination *)
      let ind = ind - 2 in
      ignore (p ~ind:ind "%s\n" epilogue)
        
        
    method dGlobal (out: out_channel) (g: global) : unit = 
      match g with 
        GFun (fdec, l) -> 
          currentFundec <- fdec;
          if debugRename then 
            ignore (E.log "Renaming for function %s\n" fdec.svar.vname);

          (* Make sure we use one return at most *)
          Oneret.oneret fdec;
          
          (* Now compute the immediate dominators. This will fill in the CFG 
           * info as well *)
          idomData <- Dominators.computeIDom fdec;
          
          (** Get the callgraph node for this function *)
          let cg_node: CG.callnode = 
            try H.find callgraph fdec.svar.vname
            with Not_found -> E.s (E.bug "Cannot find call graph info for %s"
                                     fdec.svar.vname)
          in
          
          (** Get the globals read and written *)
          let glob_read =
            (try IH.find globalsRead fdec.svar.vid
            with Not_found -> assert false) in
          let glob_read_trans = 
            (try IH.find globalsReadTransitive fdec.svar.vid
            with Not_found -> assert false) in 
          
          
          let glob_written = 
            (try IH.find globalsWritten fdec.svar.vid
            with Not_found -> assert false) in 
          let glob_written_trans = 
            (try IH.find globalsWrittenTransitive fdec.svar.vid
            with Not_found -> assert false) in 
          
          (* Compute the control flow graph info, for SSA computation *)
          let cfgi = S.prune_cfg (fundecToCFGInfo fdec) in 
          cfgInfo <- Some cfgi;
          (* Call here the SSA function to fill-in the cfgInfo *)
          S.add_ssa_info cfgi;

          (* Compute strongly connected components *)
          let scc: S.sccInfo = 
            stronglyConnectedComponents cfgi false in 
          sccInfo <- Some scc;

          (* Now do the SSA renaming. *)

          blockStartData <- Array.make cfgi.S.size (-1);
          blockEndData <- Array.make cfgi.S.size (VH.create 13);
          
          lastFreshId := 0;

          freshVars <- [];
          uninitVars <- [];
          
          if debugRename then 
            ignore (E.log "Starting renaming phase I for %s\n" 
                      fdec.svar.vname);
          Array.iteri (fun i (b: S.cfgBlock) -> 
            (* compute the initial state *)
            blockStartData.(i) <- !lastFreshId;
            if debugRename then 
              ignore (E.log "Save the rename state for block %d to %d\n"
                        i !lastFreshId);

            (* Initialize the renaming state *)
            self#initVarRenameState b;
          
            (* Now scan the block and keep track of the definitions. This is 
             * a huge hack. We try to rename the variables in the same order 
             * in which we will rename them during actual printing of the 
             * block. It would have been cleaner to print the names of the 
             * variables after printing the function.  *)
            (match b.S.bstmt.skind with 
              Instr il -> begin
                List.iter
                  (fun i -> 
                    let doCall (dest: varinfo option) (f: varinfo) : unit = 
                      let gwt: varinfo list = 
                        getGlobalsWrittenTransitive f in
                      let gwt' = 
                        match dest with 
                          Some v -> 
                            gwt @ [ v ] 
                        | _ -> gwt 
                      in
                      List.iter (fun v -> 
                        ignore (self#variableDef varRenameState v))
                        gwt'
                    in
                    match i with 
                      Set ((Var v, NoOffset), _, l)
                        when considerVariable v ->
                          currentLoc := l;
                          ignore (self#variableDef varRenameState v)
                    | Call (Some (Var v, NoOffset), 
                            Lval (Var f, NoOffset), _, l) 
                      when considerVariable v ->
                        currentLoc := l;
                        doCall (Some v) f


                    | Call (_, 
                            Lval (Var f, NoOffset), _, l) -> 
                              currentLoc := l;
                              doCall None f

                    | _ -> ())
                  il
              end
                    
            | _ -> (* No definitions *)
                ()
            );
            
            if debugRename then 
              ignore (E.log "At end of block %d:\n   @[%a@]\n"
                        i
                        (docList ~sep:line
                           (fun (v, id) -> 
                             dprintf "%s: %d" v.vname id))
                        (vhToList varRenameState));
            
            blockEndData.(i) <- VH.copy varRenameState;
          ) 
          cfgi.S.blocks;

          if debugRename then 
            ignore (E.log "Starting renaming phase II (printing) for %s\n" 
                      fdec.svar.vname);


          (** For each basic block *)
        
            
        (* The header *)
        pd (self#pLineDirective ~forcefile:true l); 

        ignore (p "%sfunction %s\n  %sformals %a%s\n  %sglobalsreadtransitive %a%s\n  %sglobalswrittentransitive %a%s\n  %slocals %a%s\n  %suninitlocals %a%s\n  %sglobalsread %a%s\n  %sglobalswritten %a%s\n  %scalls %a%s\n  %scalledby %a%s\n  %a"
          prologue fdec.svar.vname
          prologue (docList (fun v -> text (variableName v 0))) 
                  fdec.sformals epilogue
          prologue (d_list "," (fun () v -> text (variableName v 0))) 
                  (getGlobalsReadTransitive fdec.svar) epilogue
          prologue (d_list "," (fun () v -> text (variableName v 0)))
                  (getGlobalsWrittenTransitive fdec.svar) epilogue
          prologue (docList text) freshVars epilogue
          prologue (docList text) uninitVars epilogue
          prologue (d_list "," (fun () (_, v) -> text (variableName v 0))) (IH.tolist glob_read) epilogue
          prologue (d_list "," (fun () (_, v) -> text (variableName v 0))) (IH.tolist glob_written) epilogue
          prologue (U.docHash (fun k _ -> text k)) cg_node.CG.cnCallees epilogue
          prologue (U.docHash (fun k _ -> text k)) cg_node.CG.cnCallers epilogue
          (docList ~sep:line
             (fun oneScc -> 
               dprintf "%sSCC %sheaders %a%s %snodes %a%s%s\n"
                 prologue 
		 prologue (docList num) oneScc.S.headers epilogue
                 prologue (docList num) oneScc.S.nodes epilogue 
		 epilogue))
                  scc);


        (* The block *)
        self#dBlock out 2 fdec.sbody;

        (* The end *)
        ignore (p "\n%s\n\n" epilogue)

    (* Emit the globals whose address is not taken *)
    | GVarDecl (vi, l) | GVar (vi, _, l) when 
        not vi.vaddrof && isIntegralType vi.vtype 
          && not (IH.mem globalsDumped vi.vid) 
      -> 
        IH.add globalsDumped vi.vid ();
        pd (self#pLineDirective ~forcefile:true l);
        ignore (p "%sglobal %s%s\n" prologue vi.vname epilogue)
        
    | _ -> ()
end


let arithAbs (absPrinter: cilPrinter) (g: global) = 
  dumpGlobal absPrinter !arithAbsOut g

let feature : featureDescr = 
  { fd_name = "arithabs";
    fd_enabled = ref false;
    fd_description = "generation of an arithmetic abstraction";
    fd_extraopt = [
       ("--arithabs_file", Arg.String setArithAbsFile, 
        "the name of the file to dump the arithmetic abstraction to") ];
    fd_doit = 
    (function (f : file) ->
      (* Call the simplify *)
      Simplify.onlyVariableBasics := true;
      Simplify.feature.fd_doit f;
      (* Compute the call graph *)
      let graph = CG.computeGraph f in 

      (* Compute the globals written by each function *)
      IH.clear globalsWritten;
      IH.clear globalsWrittenTransitive;
      IH.clear globalsRead;

      IH.clear allFunctions;


      (* Compute the globals read and written *)
      iterGlobals 
        f
        (function
            GFun(fdec, _) -> 
              IH.replace allFunctions fdec.svar.vid (Def fdec);
              currentGlobalsRead := IH.create 13;
              IH.add globalsRead fdec.svar.vid !currentGlobalsRead;
              currentGlobalsWritten := IH.create 13;
              IH.add globalsWritten fdec.svar.vid !currentGlobalsWritten;
              ignore (visitCilBlock gwVisitor fdec.sbody)

          | GVarDecl (vd, _) when isFunctionType vd.vtype &&
                                  not (IH.mem allFunctions vd.vid) 
            -> 
              IH.add allFunctions vd.vid (Decl vd)
          | _ -> ());

      (* Now do transitive closure of the globals written by each function *)
      (* Initialize each function with the globals it writes itself *)
      IH.iter 
        (fun fid gw -> 
          IH.add globalsWrittenTransitive fid (IH.copy gw))
        globalsWritten;

      IH.iter 
        (fun fid gr -> 
          IH.add globalsReadTransitive fid (IH.copy gr))
        globalsRead;

      (* A work list initialized with all functions, that are defined *)
      let worklist: int Queue.t = Queue.create () in
      IH.iter (fun fid finfo -> 
        match finfo with 
          Def _ -> Queue.add fid worklist
        | _ -> ())
        
        allFunctions;

      (* Now run until we reach a fixed point *)
      let rec fixedpoint () = 
        try 
          let next = Queue.take worklist in 
          (* Get the function info for this one *)
          let finfo = 
            try IH.find allFunctions next
            with Not_found -> 
              E.s (E.bug "Function id=%d not in allFunctions" next)
          in
          (* If this is just a declaration, we ignore *)
          (match finfo with 
            Decl _ -> ()
          | Def fdec -> begin
              (* Find the callnode for it *)
              let cnode: CG.callnode = 
                try H.find graph fdec.svar.vname
                with Not_found -> 
                  E.s (E.bug "Function %s does not have a call node" 
                         fdec.svar.vname)
              in
              (* Union in all the variables modified by the functions this 
               * calls. Remember if we made a change. If we do, we add to the 
               * worklist the callers of this one. *)
              let changeMade = ref false in 

              (* Our written *)
              let ourWritten = 
                try IH.find globalsWrittenTransitive fdec.svar.vid
                with Not_found -> 
                  E.s (E.bug "Function %s not in globalsWrittenTransitive"
                      fdec.svar.vname)
              in

              (* Our read *)
              let ourRead = 
                try IH.find globalsReadTransitive fdec.svar.vid
                with Not_found -> 
                  E.s (E.bug "Function %s not in globalsReadTransitive"
                      fdec.svar.vname)
              in
(*
              ignore (E.log "fixedpoint: doing %s\n read so far: %a\n written so far: %a\n"
                        fdec.svar.vname
                        (docList (fun (_, v) -> text v.vname))
                        (IH.tolist ourRead)
                        (docList (fun (_, v) -> text v.vname))
                        (IH.tolist ourRead));
*)
              H.iter
                (fun n cn -> 
                  (* Get the callee's written *)
                  (try 
                    let callee_written = 
                      IH.find globalsWrittenTransitive cn.CG.cnInfo.vid in
                    IH.iter 
                      (fun gwid gw -> 
                        if not (IH.mem ourWritten gwid) then begin
                          IH.add ourWritten gwid gw;
                          changeMade := true
                        end)
                      callee_written;
                  with Not_found -> (* Callee not defined here *)
                    ());

                  (* Get the callee's read *)
                  (try 
                    let callee_read = 
                      IH.find globalsReadTransitive cn.CG.cnInfo.vid in
                    IH.iter 
                      (fun grid gr -> 
                        if not (IH.mem ourRead grid) then begin
                          IH.add ourRead grid gr;
                          changeMade := true
                        end)
                      callee_read;
                  with Not_found -> (* Callee not defined here *)
                    ());


                )
                cnode.CG.cnCallees;

              if !changeMade then begin
                H.iter 
                  (fun _ caller -> Queue.add caller.CG.cnInfo.vid worklist)
                  cnode.CG.cnCallers
              end
          end);

          fixedpoint ();
                
        with Queue.Empty -> ()
      in
      fixedpoint ();
      

      let absPrinter: cilPrinter = new absPrinterClass graph in 
      IH.clear globalsDumped;
      iterGlobals f
        (arithAbs absPrinter);

      (* compute SCC for the call-graph *)
      let nodeIdToNode: CG.callnode IH.t = IH.create 13 in
      let funidToNodeId: int IH.t = IH.create 13 in 
      let nrNodes = ref 0 in 
      let mainNode = ref 0 in 
      H.iter 
        (fun vn cn -> 
          if vn= "main" then mainNode := !nrNodes;
          IH.add nodeIdToNode !nrNodes cn;
          IH.add funidToNodeId cn.CG.cnInfo.vid !nrNodes;
          incr nrNodes) graph;

      let ci: S.cfgInfo = 
        { S.name = "call-graph";
          S.start = !mainNode;
          S.size = !nrNodes;
          S.successors = Array.make !nrNodes [];
          S.predecessors = Array.make !nrNodes [];
          S.blocks = Array.make !nrNodes { S.bstmt = mkEmptyStmt ();
                                           S.instrlist = [];
                                           S.livevars = [];
                                           S.reachable = true };
         S.nrRegs = 0;
         S.regToVarinfo = Array.create 0 dummyFunDec.svar;
        }
      in
      let ci = ci in
      nrNodes := 0;
      IH.iter (fun idx cn -> 
        let cnlistToNodeList (cnl: (string, CG.callnode) H.t) : int list = 
          Util.list_map 
            (fun (_, sn) -> 
              try IH.find funidToNodeId sn.CG.cnInfo.vid
              with Not_found -> assert false
            )
            (U.hash_to_list cnl)
        in
        (* we want to construct the callee graph not the caller graph *)
        ci.S.successors.(idx) <- cnlistToNodeList cn.CG.cnCallers;
        ci.S.predecessors.(idx) <- cnlistToNodeList cn.CG.cnCallees; 
           
        ) nodeIdToNode;

      let scc: S.sccInfo =
        stronglyConnectedComponents ci false in 
      List.iter 
        (fun oneScc -> 
          ignore (p "%sSCC %sheaders %a%s %snodes %a%s%s\n"
                    prologue 
		    prologue (docList 
                       (fun h -> 
                         (try 
			   text (IH.find nodeIdToNode h).CG.cnInfo.vname
                         with Not_found -> assert false)))
                    oneScc.S.headers epilogue
                    prologue (docList 
                       (fun n -> 
                         (try text (IH.find nodeIdToNode n).CG.cnInfo.vname
                         with Not_found -> assert false)))
                    oneScc.S.nodes epilogue
		    epilogue))
        scc;


   );
        
        
      

    fd_post_check = false;
  } 
