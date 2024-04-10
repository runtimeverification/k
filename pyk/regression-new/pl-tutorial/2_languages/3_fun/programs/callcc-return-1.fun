// using callcc for returning: grab caller's continuation

let f l return =
  if null? l
  then return 0
  else return 1;
  0 / 0
in callcc (f [])
