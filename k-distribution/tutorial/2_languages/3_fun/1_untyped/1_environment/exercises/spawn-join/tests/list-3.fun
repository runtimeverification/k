// testing letrec and multiple arguments with currying

letrec second l x = head (tail l)
in second [1, 3, 5, 2, 4, 0, -1, -5] true

// 3
