// both maximum of a list and factorial: testing various things:
// a) multiple bindings in a letrec
// b) multiple arguments to functions (max)
// c) shadowing parameters (let x = ... x ... in ... x ...)

letrec max l x y =
  if null?(cdr l)
  then car l
  else let x = max(cdr l) x y
       in if (x <= car l)
          then car l
          else x
and factorial x =
  if x <= 0
  then 1
  else x * factorial(x - 1)
in factorial (max [1, 3, factorial 4, 2, 5, 0, -1, -5] true 5)

// 620448401733239439360000
