datatype 'a mylist = Nil | Cons('a, 'a mylist)

letrec length = fun Nil -> 0 | Cons(h,t) -> 1 + length t
in length Cons(3, Cons(5, Cons(8, Nil)))
