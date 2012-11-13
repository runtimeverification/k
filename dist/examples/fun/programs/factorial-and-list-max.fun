// both maximum of a list and factorial: testing various things:
// a) multiple bindings in a letrec
// b) multiple arguments to functions (max)
// c) shadowing parameters (let x = ... x ... in ... x ...)


rec max = fun [h] x y -> h
          |   [h|t] x y -> let x = max t x y
                           in  if h > x then h else x
and f = fun 0 -> 1
        |   x -> x * f(x - 1)
in f (max [1, 3, f 4, 2, 5, 0, -1, -5] true 5)

// 620448401733239439360000
