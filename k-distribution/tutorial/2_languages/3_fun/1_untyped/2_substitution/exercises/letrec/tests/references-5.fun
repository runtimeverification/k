// testing &, *, := and lists

let f x = x := @x + 1
and x = 7
in [x, f &x; x, f &x; x]

// [7,8,9], or [7,9,8], or [9,8,9], or [9,9,8]
