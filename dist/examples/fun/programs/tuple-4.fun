// testing two tuple arguments to a function
// we get a kast parsing error if we remove the parentheses around the function
// "(fun (x,y) -> x * y)", which is annoying.  kast needs to be fixed.

let f (a,b) (x,y) = a(x,y) + b(x,y)
in f ((fun (x,y) -> x * y), fun (x,y) -> x + y) (10,20)
