datatype 'a bst = Empty | Node('a bst, 'a, 'a bst)

letrec bst_sort l = flatten (mk_bst l)
   and flatten = fun Empty -> [] 
                   | Node(l,n,r) -> append (flatten l) (cons n (flatten r))
   and append = fun [] r -> r | [h|t] r -> cons h (append t r)
   and mk_bst = fun [] -> Empty | [h|t] -> insert (mk_bst t) h
   and insert = fun Empty n -> Node(Empty,n,Empty)
                  | Node(l, m, r) n -> if n < m
                                       then Node(insert l n, m, r)
                                       else Node(l, m, insert r n)
   and downto = fun 0 -> [0] | n -> cons n (downto (n - 1))
   and upto = fun 0 -> [0] | n -> append (upto (n - 1)) [n]
   and merge = fun [] [] -> []
                 | [h1|t1] [h2|t2] -> cons h1 (cons h2 (merge t1 t2))
   and shuffle n = merge (downto n) (upto n)
in (bst_sort (shuffle 10))
