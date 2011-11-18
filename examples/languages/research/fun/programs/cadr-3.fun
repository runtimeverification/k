// testing letrec and multiple arguments with currying

letrec cadr l x = (car (cdr l))
in cadr [1, 3, 5, 2, 4, 0, -1, -5] true

// 3
