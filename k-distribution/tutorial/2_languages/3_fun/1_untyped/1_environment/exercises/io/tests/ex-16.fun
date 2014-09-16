letrec print_list l = print "[";
                      letrec print_list_aux =
                        fun [] b -> 0
                          | [h|t] b -> if b then print ", " else 0;
                                       print h;
                                       print_list_aux t true
                      in print_list_aux l false;
                      print "]"
and nat = fun 0 -> []
            | n -> cons n (nat (n-1))
in (print "List of elements down from: "; print_list (nat read))
