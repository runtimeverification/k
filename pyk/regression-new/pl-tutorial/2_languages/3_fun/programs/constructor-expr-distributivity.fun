datatype exp = Value(string) | Plus(exp,exp) | Minus(exp,exp) | Times(exp,exp)

letrec toString =
   fun   Value(n) -> n
     |  Plus(l,r) -> "(" ^ toString(l) ^ " + " ^ toString(r) ^ ")"
     | Minus(l,r) -> "(" ^ toString(l) ^ " - " ^ toString(r) ^ ")"
     | Times(l,r) -> toString(l) ^ " * " ^ toString(r)
   and distribute =
   fun Times(e1, Plus(e2, e3)) -> Plus(Times(distribute e1, distribute e2),
                                       Times(distribute e1, distribute e3))
     | Times(Plus(e1, e2), e3) -> Plus(Times(distribute e1, distribute e3),
                                       Times(distribute e2, distribute e3))
     | Plus(l,r) -> Plus(distribute l, distribute r)
     | Minus(l,r) -> Minus(distribute l, distribute r)
     | Value(n) -> Value(n)
in toString (distribute Times(Value("n"), Plus(Value("x"), Value("y"))))
