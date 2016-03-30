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

type step = Step of k * step_function | NoStep of k

let rec take_steps (module Def: Plugin.Definition) (step_function: k -> (k * step_function)) (active_threads: k list) (config: k) (depth: int) (n: int) (last_resort: bool) : k * int =
  if n = depth then (
    config,n
  ) else (
    match active_threads with
    | thread :: other_active_threads ->
    let active_config = context_switch config thread in
      match (try let res,func = (step_function active_config) in Step(res,func) with Stuck c -> NoStep c) with
      | Step (([Thread(_,thread_id,_,[Map(_,_,other_threads)])] as config),(StepFunc step_function)) -> (
        take_steps (module Def) step_function (thread_id :: other_active_threads) config depth (n+1) false
      )
      | NoStep config -> (
        match active_config with [Thread(_,thread_id,_,[Map(_,_,other_threads)])] ->
        if other_active_threads = [] then (
          if last_resort || KMap.cardinal other_threads = 0 then (
            config,n
          ) else (
            let (other_thread_ids,_) = List.split(KMap.bindings other_threads) in
            take_steps (module Def) Def.step (thread_id :: other_thread_ids) active_config depth n true
          )
        ) else (
          take_steps (module Def) Def.step other_active_threads active_config depth n last_resort
        )
      )
  )
          

let run (config: k) (depth: int) : k * int =
  let module Def = (val Plugin.get () : Plugin.Definition) in
  let first_config, first_thread_ids = split_config config in
  let last_config,n = take_steps (module Def) Def.step first_thread_ids first_config depth 0 false in
  (plug_config last_config, n)
