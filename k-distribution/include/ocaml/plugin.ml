open Constants
open Constants.K
open Prelude

module type Definition =
sig
  val eval : normal_kitem -> k -> k
  val get_thread_set : k -> k
  val set_thread_set : k -> k -> k
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
  Dynlink.loadfile filename
