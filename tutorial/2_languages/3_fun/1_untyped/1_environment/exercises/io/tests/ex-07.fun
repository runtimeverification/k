letrec all n p = if n<0
                 then 0
                 else ( print "Element ";
                        print p;
                        print " is ";
                        print n;
                        print "\n";
                        all (n - 1) (p + 1) )
in all 10 1
