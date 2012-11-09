letrec factorial x =
  if x<=0
  then 1
  else x * factorial(x - 1)
in factorial(factorial 4)

// 620448401733239439360000
