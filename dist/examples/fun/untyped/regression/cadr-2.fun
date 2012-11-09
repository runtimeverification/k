// testing letrec

letrec cadr l = (car (cdr l))
in cadr [1, 3, 5, 2, 4, 0, -1, -5]

// 3
