letrec length = fun [] -> 0
                |   [h|t] -> 1 + length t
and   complex = fun {[{h1,h2}|t],l,[{a,2},{3,b},c]} -> {h2 + length t + b, a}
                |   {[],[],[{7,2},x,c]}             -> x
                |   p                               -> {0,0}
and     map f = fun []    -> []
                |   [h|t] -> cons (f h) (map f t)
in map complex [{[{8,7}],[],[{9,2},{3,3},{2,2}]},
                {[],[],[{7,2},{0,1},{-1,-1}]},
                {[],[],[]}]
