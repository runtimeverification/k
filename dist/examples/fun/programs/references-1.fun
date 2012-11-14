letrec

max l {x,y} =
  if @x != y
  then -1
  else if null?(tail l)
       then head l
       else let x = max (tail l) {x := @x + 1; x, y + 1}
            in if x <= head l
               then head l
               else x

and 

map f l = 
  if null? l
  then []
  else cons (f (head l)) (map f (tail l))

and

factorial x =
  if x <= 0
  then 1
  else x * factorial(x - 1)

in max (map factorial [1, 2, 3, 4, 5, factorial 5]) {ref 1, 1}
