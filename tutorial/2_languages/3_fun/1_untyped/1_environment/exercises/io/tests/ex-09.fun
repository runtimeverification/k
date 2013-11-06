let print_list l = print "[";
                   letrec print_list_aux =
                     fun [] b -> 0
                       | [h|t] b -> if b then print ", " else 0;
                                    print h;
                                    print_list_aux t true
                   in print_list_aux l false;
                   print "]"
in print_list [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
