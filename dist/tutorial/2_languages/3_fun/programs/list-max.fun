letrec max = fun [h] -> h
             |   [h|t] -> let x = max t
                          in  if h > x then h else x
in max [1, 3, 5, 2, 4, 0, -1, -5]

// 5
