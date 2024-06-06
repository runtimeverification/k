// using callcc for returning: grab callee's continuation

let f l =
  callcc (fun return -> 
            if null?(l)
            then return 0
            else return 1;
            0 / 0
          )
in f [1,2]
