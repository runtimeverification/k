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

let init_thread_pool (threads: k list) : k list * int * bool = (threads, 0, false)

let schedule_next_thread (module Def: Plugin.Definition) (step_function: k -> (k * step_function)) (stuck: bool) (config: k) (thread_pool: k list * int * bool) : (k * (k -> (k * step_function)) * (k list * int * bool)) option =
  let slice = 5000 in
  let (pool_threads, slice_used, last_resort) = thread_pool in
  if not stuck && slice_used < slice then Some (config, step_function, (pool_threads, slice_used + 1, false))
  else (
    match config with
      | [Thread(_,curr_thread,_,[Map(_,_,other_threads)])] -> (
        let (other_thread_ids,_) = List.split(KMap.bindings other_threads) in
        let is_active (thd: k) : bool = List.mem thd other_thread_ids in
        let new_pool_threads = List.filter is_active (if stuck then pool_threads else pool_threads@[curr_thread]) in
        match new_pool_threads with
          | [] -> (
            if last_resort then (
              None
            ) else (
              let all_threads = other_thread_ids@[curr_thread] in
              let config = context_switch config (List.hd all_threads) in
              Some (config, Def.step, (List.tl all_threads, 0, true))
            )
          )
          | (thread :: threads) -> (
            let config = context_switch config thread in
            Some (config, Def.step, (threads, 0, last_resort))
          )
        )
      | _ -> invalid_arg ("mismatched constructor at top of split configuration: " ^ (print_k config))
  )

let rec take_steps (module Def: Plugin.Definition) (step_function: k -> (k * step_function)) (thread_pool: (k list * int * bool)) (config: k) (depth: int) (n: int) : k * int =
  if n = depth then (config, n)
  else (
    match (try let res,func = (step_function config) in Step(res,func) with Stuck c -> NoStep c) with
    | Step (config,(StepFunc step_function)) -> (
        match schedule_next_thread (module Def) step_function false config thread_pool with
          | None -> (config, n)
          | Some (config, step_function, thread_pool) -> take_steps (module Def) step_function thread_pool config depth (n+1)
    )
    | NoStep config -> (
      match schedule_next_thread (module Def) step_function true config thread_pool with
        | None -> (config, n)
        | Some (config, step_function, thread_pool) -> take_steps (module Def) step_function thread_pool config depth n
    )
  )

let rec take_steps_no_thread (module Def: Plugin.Definition) (step_function: k -> (k * step_function)) (config: k) (depth: int) (n: int) : k * int =
  if n = depth then (
    (config, n)
  ) else (
    match (try let (res, func) = (step_function config) in Step(res, func) with Stuck c -> NoStep c) with
    | Step(config, StepFunc step_function) -> take_steps_no_thread (module Def) step_function config depth (n+1)
    | NoStep config -> (config, n)
  )

let rec strat_run (module Def: Plugin.Definition) (config: k) (depth: int) (n: int) : k * int =
  let c0,threads = split_config config in
  let c0 = context_switch c0 (List.hd threads) in
  let c1,n1 = take_steps (module Def) Def.step (init_thread_pool (List.tl threads)) c0 depth n in

  let c1,threads = split_config (Def.make_stuck (plug_config c1)) in
  let c1 = context_switch c1 (List.hd threads) in
  let c2,n2 = take_steps (module Def) Def.step (init_thread_pool (List.tl threads)) c1 depth n1 in

  if (n1 = n2) then (plug_config c2, n2) else (strat_run (module Def) (plug_config c2) depth n2)

let run (config: k) (depth: int) : k * int =
  let module Def = (val Plugin.get () : Plugin.Definition) in
  let result = strat_run (module Def) config depth 0 in
  Hooks.IO.flush_logs ();
  result

let rec strat_run_no_thread_opt (module Def: Plugin.Definition) (config: k) (depth: int) (n: int) : k * int =
  let c1,n1 = take_steps_no_thread (module Def) Def.step config depth n in
  let c2,n2 = take_steps_no_thread (module Def) Def.step (Def.make_stuck c1) depth n1 in
  if (n1 = n2) then (c2, n2) else (strat_run_no_thread_opt (module Def) c2 depth n2)

let run_no_thread_opt (config: k) (depth: int) : k * int =
  let module Def = (val Plugin.get () : Plugin.Definition) in
  let result = strat_run_no_thread_opt (module Def) config depth 0 in
  Hooks.IO.flush_logs ();
  result

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
