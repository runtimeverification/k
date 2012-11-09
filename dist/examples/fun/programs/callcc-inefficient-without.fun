// calculating the product of elements in a list
// this is inefficient; one would like to throw an exception
// see callcc-efficient-with.fun for an efficient variant

letrec f l =
  if null?(l)
  then 1
  else if (car l) == 0
       then 0
       else (car l) * f(cdr l)
in f [1,2,3,4,5,6,7,8,9,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,8,9]
