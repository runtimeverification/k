// testing ref, * and ;

let f x = x + x
in let y = ref 5
   in f (y := @y + 3; @y)

// 16
