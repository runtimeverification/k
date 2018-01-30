// testing tuple arguments to a function

datatype nothing = Nothing
datatype ('a,'b) pair = Pair('a,'b)

let f = fun Nothing Pair(a,b) q Nothing Pair(x,y) Nothing
          -> a Pair(x,y) + b Pair(x,y)
in f Nothing Pair(fun Pair (x,y) -> x * y, fun Pair(x,y) -> x + y)
       3 Nothing Pair(10,20) Nothing
