let* x = 1
and  y = let x = x in x
and  z = let x = y + 1 in x
and  u = x
in u
