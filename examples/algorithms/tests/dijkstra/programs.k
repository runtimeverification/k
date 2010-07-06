kmod DIJKSTRA-PROGRAMS is including DIJKSTRA
  ops a b c d e f : -> Id
  op p1 : -> Set
  macro p1 = (a - 3 -> b)
             (b - 2 -> f)
             (a - 3 -> c)
             (c - 1 -> f)
             (a - 2 -> d)
             (d - 1 -> e)
             (e - 1 -> f)
             (a - 4 -> e)
endkm
