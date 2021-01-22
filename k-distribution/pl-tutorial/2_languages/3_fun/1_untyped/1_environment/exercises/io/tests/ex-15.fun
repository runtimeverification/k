letrec hanoi = fun 0 a b c -> 0
                 | n a b c -> hanoi (n-1) a c b;
                              print a; print " -> "; print b; print "\n";
                              hanoi (n-1) c b a
in (print "Number of discs: "; hanoi read "a" "b" "c")
