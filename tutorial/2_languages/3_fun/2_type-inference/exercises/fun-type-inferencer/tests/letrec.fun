letrec h = f
and    f = fun n -> if n>0 then g(n - 1) else (fun x -> x)
and    g = fun n -> if n>0 then h(n - 1) else (fun x -> x)
in h

/*

Step 1: Adding fresh types for all variables

h |-> Th
f |-> Tf
g |-> Tg

Step 2: Ayping all the RHS expressions and generating constraints

Tg  = int -> Trg
Trg = T1 -> T1
Th  = int -> Trh
Trh = T2 -> T2

Step 3: Adding constraints for each binder

Th  = Tf
Tf  = int -> Trg
Tg  = int |-> Trh

Current Mgu is

Th  = int -> T1 -> T1
Tf  = int -> T1 -> T1
Tg  = int -> T1 -> T1
Trg = T1 -> T1
Trh = T1 -> T1
T2  = T1

Step 4: Generating each parametric type and writing it into the TEnv

Th  = (forall T1) int -> T1 -> T1
Tf  = (forall T1) int -> T1 -> T1
Tg  = (forall T1) int -> T1 -> T1

All types above are parametric, despite the T2 type variable appearing
in both Tf and Th.
 
*/
