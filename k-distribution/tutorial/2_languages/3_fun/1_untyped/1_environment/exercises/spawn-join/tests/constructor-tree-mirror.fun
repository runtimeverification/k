datatype 'a tree = Leaf('a) | Tree('a tree, 'a tree)

letrec mirror =
   fun Leaf(n) -> Leaf(n)
     | Tree(left, right) -> Tree(mirror(right), mirror(left))
in mirror Tree(Tree(Leaf(1), Leaf(2)),
               Tree(Leaf(3), Tree(Leaf(4), Leaf(5))))
