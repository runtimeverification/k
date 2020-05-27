let () = Plugin.load Sys.argv.(1)
open Prelude
open Run
let () = Sys.catch_break true
let () = Gc.set { (Gc.get()) with Gc.minor_heap_size = 33554432 }let serialize, input, file = Makeconfig.marshal ()
let str = if serialize then Marshal.to_string (input : Prelude.k) [] else print_k_binary input
let () = output_string file str
