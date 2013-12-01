// using callcc for looping


let goto = ref (fun x -> x) and n = ref 0
in callcc (fun exit -> 
             callcc (fun k -> goto := k; 0);   // "goto _" will jump here
             if @n < 100 then n := @n + 1 else exit @n;
             @goto 0)
