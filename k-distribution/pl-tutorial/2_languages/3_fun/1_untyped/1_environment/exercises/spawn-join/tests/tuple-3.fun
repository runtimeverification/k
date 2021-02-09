// testing functions taking tuple arguments

datatype ('a,'b,'c) triple = Triple('a,'b,'c)

let f Triple(x,y,z) = x + y + z
in f Triple(1,2,3)
