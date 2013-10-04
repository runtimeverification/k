// testing &, *, := and lists

let f x = x := @x + 1
and x = 7
in [x, f &x; x, f &x; x]
