// testing nested tuples

datatype 'a wrapper = Wrapper('a)
datatype ('a,'b) pair = Pair('a,'b)

let x = 1
and y = Wrapper(2)
and z = Pair(3,4)
in Pair(Pair(x,y),z)
