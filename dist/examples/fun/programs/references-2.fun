let f x y = x := @x + 2; y := @y + 3
and x = ref 0
in (f x x; @x)

// 5
