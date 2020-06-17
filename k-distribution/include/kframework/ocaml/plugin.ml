open Constants
open Prelude

module type Definition =
sig
  val eval : normal_kitem -> k -> k
  val get_thread_set : k -> k
  val set_thread_set : k -> k -> k
  val make_stuck : k -> k
  val make_unstuck : k -> k
  val step : k -> (k * step_function)
end

let the_definition = ref None
let get () : (module Definition) =
  match !the_definition with
  | Some s -> s
  | None -> failwith "Definition not loaded"

let load (path: string) : unit =
  let () = Dynlink.allow_unsafe_modules true in
  let filename = Dynlink.adapt_filename (path) in
  try Dynlink.loadfile filename
  with Dynlink.Error e -> prerr_string (Dynlink.error_message e); failwith "could not load semantics"
