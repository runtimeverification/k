// testing letrec: next should get stuck

let x = 1
in letrec x = 2
   and y = x
   in y
