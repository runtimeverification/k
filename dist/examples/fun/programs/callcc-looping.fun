// using callcc for looping

let goto = 0 and n = 0
in callcc (fun exit -> 
             callcc (fun k -> &goto := k);   // "goto _" will jump here
             if n < 100 then &n := n + 1 else exit n;
             goto 0)
