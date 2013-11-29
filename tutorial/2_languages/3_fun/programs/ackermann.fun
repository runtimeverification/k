datatype ('a,'b) pair = Pair('a,'b)

letrec ack = fun Pair(0,n) -> n + 1
             |   Pair(m,0) -> ack Pair(m - 1, 1)
             |   Pair(m,n) -> ack Pair(m - 1, ack Pair(m, n - 1))
in (ack Pair(2,3))
