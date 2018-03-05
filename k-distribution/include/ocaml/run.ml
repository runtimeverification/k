open Constants
open Constants.K
open Prelude

let split_config (config: k) : k * k list =
  let module Def = (val Plugin.get () : Plugin.Definition) in
  match Def.get_thread_set config with
  | [Map(sort,lbl,thread_set)] ->
  (let (first_thread_id,first_thread) = try KMap.choose thread_set with Not_found -> ([Bottom], [Bottom]) in
  let first_other_threads = KMap.remove first_thread_id thread_set in
  let first_global = Def.set_thread_set config [ThreadLocal] in
  let first_other_thread_ids, _ = List.split(KMap.bindings first_other_threads) in
  [Thread(first_global,first_thread_id,first_thread,[Map(sort,lbl,first_other_threads)])], first_thread_id :: first_other_thread_ids)
  | _ -> failwith "split_config"

let plug_config (config: k) : k =
  let module Def = (val Plugin.get () : Plugin.Definition) in
  match config with [Thread(global,thread_id,thread,[Map(sort,lbl,threads)])] ->
  let thread_set = [Map(sort,lbl,(KMap.remove [Bottom] (KMap.add thread_id thread threads)))] in
  Def.set_thread_set global thread_set
  | _ -> config

let context_switch (config: k) (thread_id: k) : k = match config with
  [Thread(global,old_thread_id,old_thread,[Map(sort,lbl,other_threads)])] ->
  if (K.compare old_thread_id thread_id) = 0 then config else
  [Thread(global,thread_id,(KMap.find thread_id other_threads),[Map(sort,lbl,(KMap.remove thread_id (KMap.add old_thread_id old_thread other_threads)))])]
| _ -> invalid_arg "context switch"

type step = Step of k * step_function | NoStep of k

let strat_step (module Def: Plugin.Definition) (step_function: k -> (k * step_function)) (config: k) : k * step_function =
  try
    step_function config
  with Stuck _ ->
    step_function (Def.make_stuck config)

let rec take_steps (module Def: Plugin.Definition) (step_function: k -> (k * step_function)) (thread: k) (other_active_threads: k list) (config: k) (depth: int) (n: int) (last_resort: bool) : k * int =
  if n = depth then (
    config,n
  ) else (
    let active_config = context_switch config thread in
      match (try let res,func = (strat_step (module Def) step_function active_config) in Step(res,func) with Stuck c -> NoStep c) with
      | Step (([Thread(_,thread_id,_,_)] as config),(StepFunc step_function)) -> (
        take_steps (module Def) step_function thread_id other_active_threads config depth (n+1) false
      )
      | Step _ -> invalid_arg "mismatched constructor at top of split configuration"
      | NoStep config -> (
        match active_config with [Thread(_,thread_id,_,[Map(_,_,other_threads)])] -> (
          let (other_thread_ids,_) = List.split(KMap.bindings other_threads) in
          let still_active (thd: k) : bool = List.mem thd other_thread_ids in
          let still_active_threads = List.filter still_active other_active_threads in
          match still_active_threads with
          | [] -> (
            if last_resort || KMap.cardinal other_threads = 0 then (
              config,n
            ) else (
              take_steps (module Def) Def.step thread_id other_thread_ids active_config depth n true
            )
          )
          | thread_id :: other_still_active_threads -> (
            take_steps (module Def) Def.step thread_id other_still_active_threads active_config depth n last_resort
          )
        )
        | _ -> invalid_arg "mismatched constructor at top of split configuration"
      )
  )

let rec take_steps_no_thread (module Def: Plugin.Definition) (step_function: k -> (k * step_function)) (config: k) (depth: int) (n: int) : k * int =
  if n = depth then (
    (config, n)
  ) else (
    match (try let (res, func) = (strat_step (module Def) step_function config) in Step(res, func) with Stuck c -> NoStep c) with
    | Step(config, StepFunc step_function) -> take_steps_no_thread (module Def) step_function config depth (n+1)
    | NoStep config -> (config, n)
  )

let run (config: k) (depth: int) : k * int =
  let module Def = (val Plugin.get () : Plugin.Definition) in
  let first_config, first_thread_ids = split_config config in
  let last_config,n = take_steps (module Def) Def.step (List.hd first_thread_ids) (List.tl first_thread_ids)  first_config depth 0 false in
  (plug_config last_config, n)

let run_no_thread_opt (config: k) (depth: int) : k * int =
  let module Def = (val Plugin.get () : Plugin.Definition) in
  take_steps_no_thread (module Def) Def.step config depth 0

module Makeconfig =
struct
  let depth = ref (-1)
  let output_file = ref "run.out"
  let name = ref ""
  let value = ref ""
  let init = ref "initGeneratedTopCell"
  let vars = ref KMap.empty
  let term = ref []
  let serialize = ref false
  let is_marshal = ref false
  let is_term = ref false

  let add_arg category =
    if !is_marshal && not !serialize then Prelude.no_parse_eval := true;
    let parsed_val = match category with
    | "text" -> Lexer.parse_k !value
    | "textfile" -> Lexer.parse_k_file !value
    | "binary" -> Lexer.parse_k_binary_string !value
    | "binaryfile" -> Lexer.parse_k_binary_file !value
    | _ -> raise (Arg.Bad "invalid kast format. Choose one of text|textfile|binary|binaryfile")
    in if !name = "" then begin
      term := parsed_val;
      is_term := true
    end else
      let key = [KToken(SortKConfigVar, "$" ^ !name)] in
      vars := KMap.add key parsed_val !vars

  let types = ["text"; "textfile"; "binary"; "binaryfile"]

  let speclist = [
    ("--depth", Arg.Set_int depth, "The maximum number of computational steps to execute the definition for.");
    ("--output-file", Arg.Set_string output_file, "The file to write the resulting configuration into.");
    ("-c", Arg.Tuple([Arg.Set_string name; Arg.Set_string value; Arg.Symbol(types, add_arg)]), "A krun configuration variable.");
    ("-t", Arg.Tuple([Arg.Set_string value; Arg.Symbol(types, add_arg)]), "The entire term to interpret.");
    ("--initializer", Arg.Set_string init, "Initializer for top cell.");
    ("-s", Arg.Set serialize, "Output term marshaled.")
  ]

  let usage_msg = "K interpreter"

  let parse () : (k * int * out_channel) =
    Arg.parse speclist (fun _ -> ()) usage_msg;
    let module Def = (val Plugin.get () : Plugin.Definition) in
    let input = if !is_term then !term else Def.eval (Constants.KApply(Constants.parse_klabel(!init), [[Map(SortMap,Lbl_Map_,!vars)]])) [] in
    vars := KMap.empty; (* for gc *)
    input, !depth, open_out_bin !output_file

  let marshal () =
    is_marshal := true;
    Arg.parse speclist (fun _ -> ()) usage_msg;
    let input = [Map(SortMap,Lbl_Map_,!vars)] in
    !serialize, input, open_out_bin !output_file
end
