letrec length = fun [] -> 0
                |   [h|t] -> 1 + length t
in length [1, 3, 5, 2, 4, 0, -1, -5]

// 8
