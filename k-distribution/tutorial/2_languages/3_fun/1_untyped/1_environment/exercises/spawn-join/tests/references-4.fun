// can be used for testing parameter passing styles
// replace parameter passing style of f

let f = let c = ref 0
        in (
             c := @c + 100 ;
             (fun x -> c := @c + 1000; x + x + @c)
           )
in let y = ref 0
   in f(y := @y + 1 ; @y) + f(0)
