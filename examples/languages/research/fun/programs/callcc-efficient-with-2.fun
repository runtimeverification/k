--- the following is also efficient and uses try/catch

let f l = try (
            letrec aux l =
              if null?(l)
              then 1
              else if (car l) == 0
                   then throw 0
                   else (car l) * aux(cdr l)
            in aux l
          ) catch(x)
            x
in f [1,2,3,4,5,6,7,8,9,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,8,9]
