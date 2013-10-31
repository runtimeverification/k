letrec toString =
   fun   Value(n) -> n
     |  Plus(l,r) -> "(" + toString(l) + " + " + toString(r) + ")"
     | Minus(l,r) -> "(" + toString(l) + " - " + toString(r) + ")"
     | Times(l,r) -> toString(l) + " * " + toString(r)
in toString Times(Value("n"), Plus(Value("x"), Value("y")))
