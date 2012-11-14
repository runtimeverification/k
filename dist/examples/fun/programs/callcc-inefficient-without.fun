// calculating the product of elements in a list
// this is inefficient; one would like to throw an exception
// see callcc-efficient-with.fun for an efficient variant

letrec f l =
  if null? l
  then 1
  else if head l == 0
       then 0
       else head l * f(tail l)
in f [1,2,3,4,5,0,6,7,8,9]
