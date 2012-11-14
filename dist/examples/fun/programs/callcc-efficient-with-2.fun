// the following is also efficient and uses try/catch

let f l = try 
            letrec aux l =
              if null? l
              then 1
              else if head l == 0
                   then throw 0
                   else head l * aux(tail l)
            in aux l
          catch(x)
            x
in f [1,2,3,4,5,0,6,7,8,9]
