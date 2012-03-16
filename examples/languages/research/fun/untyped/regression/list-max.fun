letrec max l =
  if null?(cdr l)
  then car l
  else let x = max (cdr l)
       in if (x <= car l)
          then car l
          else x
in max [1, 3, 5, 2, 4, 0, -1, -5]

// 5
