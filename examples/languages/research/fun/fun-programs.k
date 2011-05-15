kmod FUN-PROGRAMS is including FUN-SYNTAX
  syntax Id ::= a | b | c | d | e | f | g | h | i | j | k 
              | l | m | n | o | p | q | r | s | t | u | v | w | x | y | z
              | factorial | max | map | return | throw | aux | continuation | value | exit | goto | cadr
              | f00 | f01 | f02 | f03 | f04 | f05 | f06 | f07 | f08 | f09 | f10 | f11 | f12 | f13 | f14

  syntax Exp ::= p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 | p12 | p13 | p14 
               | p15-1 | p15-2 | p16 | p17 | p18 | p19 | p20 | p21 | p22 | p23 | p24 | p25 
               | p26-1 | p26-2 | p27-1 | p27-2 | p27-3 | p28 | p29 | p30 | p31


--- factorial
  macro p1 = (
    letrec factorial x = if x<=0 then 1 else x * factorial(x - 1)
    in factorial (factorial 4)
  )
---620448401733239439360000


--- maximum of a list
  macro p2 = (
    letrec max l =
             if null?(cdr l)
             then car l
             else let x = max (cdr l)
                  in if (x <= car l)
                     then car l
                     else x
    in max [1, 3, 5, 2, 4, 0, -1, -5]
  )
--- 5


--- second element in a list: testing let
  macro p3 = (
    let cadr l = (car (cdr l))
    in cadr [1, 3, 5, 2, 4, 0, -1, -5]
  )
--- 3


--- second element in a list: testing letrec
  macro p4 = (
    letrec cadr l = (car (cdr l))
    in cadr [1, 3, 5, 2, 4, 0, -1, -5]
  )
--- 3


--- second element in a list: testing letrec and multiple arguments
  macro p4 = (
    letrec cadr l x = (car (cdr l))
    in cadr [1, 3, 5, 2, 4, 0, -1, -5] true
  )
--- 3


--- testing tuple binding
  macro p6 = (
    let (x,y,z) = (1,2,3)
    in x + y + z
  )


--- testing functions tuple arguments and polymorphism
  macro p21 = (
    fun (x,y,z) -> y
  )
--- some closure


--- testing functions taking tuple arguments
  macro p7 = (
    let f(x,y,z) = x + y + z
    in f(1,2,3)
  )


  macro p8 = (
    let f (a, b) (x, y)	= a(x,y) + b(x,y)
    in f (fun (x, y) -> x * y, fun (x, y) -> x + y) (1,2)
  )


--- both maximum of a list and factorial: testing various things:
--- a) multiple bindings in a letrec
--- b) multiple arguments to functions (max)
--- c) shadowing parameters (let x = ... x ... in ... x ...)
  macro p5 = (
    letrec
      max l x y
        = if null?(cdr l)
          then car l
          else let x = max(cdr l) x y
               in if (x <= car l)
                  then car l
                  else x
    and
      factorial x
        = if x <= 0
          then 1
          else x * factorial(x - 1)
    in factorial (max [1, 3, factorial 4, 2, 5, 0, -1, -5] true 5)
  )
---620448401733239439360000


  macro p9 = (
    letrec
      max l (x, y) =
        if (* x) != y
        then -1
        else if null?(cdr l)
             then (car l)
             else let x = max (cdr l) ((x := (* x) + 1 ; x), y + 1)
                  in if (x <= car l)
                     then (car l)
                     else x
    and
      map f l = 
        if null? l
        then []
        else cons (f (car l)) (map f (cdr l))
    and
      factorial x =
        if x <= 0
        then 1
        else x * factorial(x - 1)
    in max (map factorial [1, 2, 3, 4, 5, factorial 5]) (ref 1, 1)
  )


--- testing ref * ;
  macro p10 = (
    let f x y = (x := (* x) + 2 ; y := (* y) + 3)
    and x = ref 0
    in (f x x ; * x)
  )
--- 5


--- testing letrec: next should get stuck
  macro p11 = (
    let x = 1
    in letrec x = 2
       and    y = x
       in y
  )


--- testing ref, * and ;
  macro p12 = (
    let f x = x + x
    in let y = ref 5
       in f (y := (* y) + 3 ; * y)
  )


--- can be used for testing parameter passing styles
--- replace parameter passing style of f
  macro p13 = (
    let f = let c = ref 0
            in (
                 c := (* c) + 100 ;
                 fun x -> (
                            c := (* c) + 1000 ;
                            x + x + (* c)
                          )
               )
    in let y = ref 0
       in f(y := (* y) + 1 ; * y) + f(0)
  )

--- testing &, *, := and lists
  macro p14 = (
    let f x = x := *x + 1
    and x = 7
    in [x, (f(& x) ; x), (f(& x) ; x)]
  )

--- testing empty argument
  macro p15-1 = (
    let f() = 7
    in f
  )
--- some closure


--- testing empty argument
  macro p15-2 = (
    let x = 7
    in let f() = x
       in f()
  )
--- 7

--- testing polymorphism
  macro p16 = (
    let f x = x
    in f
  )
--- some closure


--- testing (instantiated) polymorphism
  macro p17 = (
    let f x = x
    in f 3
  )
--- 3


--- testing polymorphism
  macro p18 = (
    let f = fun x -> x
     in if (f true) then (f 2) else (f 3)
  )
--- 2


--- testing polymorphism
  macro p19 = (
    let f = fun x -> let y = x in y
    in (fun x -> f) 7
  )
--- identity


--- p20 justifies the restriction that reference types should not be polymorphic
--- the following runs in our semantics, but it should not type (elements of different types are added in *r)!
  macro p20 = (
    let f = let r = ref []
            in fun x -> (r := cons x (* r) ; x)
    in if f true then f 3 else f 4
  )


--- testing polymorphism and also the efficiency of the type inferencer
  macro p22 = ( 
    let f00 = fun x -> fun y -> x in
      let f01 = fun x -> f00 (f00 x) in
        let f02 = fun x -> f01 (f01 x) in
          let f03 = fun x -> f02 (f02 x) in
            let f04 = fun x -> f03 (f03 x) in
              let f05 = fun x -> f04 (f04 x) in
                let f06 = fun x -> f05 (f05 x) in
                  let f07 = fun x -> f06 (f06 x) in
                    let f08 = fun x -> f07 (f07 x) in
                       f08
  )


--- testing callcc
  macro p23 = (
    callcc (fun k -> 7)
  )
--- 7


--- testing callcc
  macro p24 = (
    callcc (fun k -> k 7)
  )
--- 7


--- testing callcc
  macro p25 = (
    callcc (fun k -> k 7 + 3)
  )
---7


--- testing callcc
  macro p30 = (
    (callcc (fun k -> 7)) + 3
  )
--- 10

--- testing callcc
  macro p31 = (
    (callcc (fun k -> k 7 + 5)) + 3
  )
--- 10


--- using callcc for returning: grab caller's continuation
  macro p26-1 = (
    let f l return = (
          if null?(l)
          then return 0
          else return 1 ;
          0 / 0
        )
    in callcc (f [])
  )


--- using callcc for returning: grab callee's continuation
  macro p26-2 = (
    let f l = callcc (fun return -> (
          if null?(l)
          then return 0
          else return 1 ;
          0 / 0
        ) )
    in f [1,2]
  )


--- calculating the product of elements in a list
--- this is inefficient; one would like to throw an exception
  macro p27-1 = (
    letrec f l =
             if null?(l)
             then 1
             else if (car l) == 0
                  then 0
                  else (car l) * f(cdr l)
    in f [1,2,3,4,5,6,7,8,9,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,8,9]
  )


--- using callcc for exceptions
--- the following is efficient
  macro p27-2 = (
    let f l = callcc (fun throw -> (
                letrec aux l =
                         if null?(l)
                         then 1
                         else if (car l) == 0
                              then throw 0
                              else (car l) * aux(cdr l)
                in aux l
              ) )
    in f [1,2,3,4,5,6,7,8,9,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,8,9]
  )


--- using callcc to define generic exceptions
  syntax Exp ::= try Exp catch ( Id ) Exp
--- assume that continuation and value are not free in E and E'
  macro try E catch(X:Id) E':Exp
      = callcc (fun continuation -> (fun throw -> E:Exp)(fun value -> continuation ((fun X -> E') value)))
--- the following is also efficient and uses try/catch
  macro p27-3 = (
    let f l = try
                letrec aux l =
                         if null?(l)
                         then 1
                         else if (car l) == 0
                              then throw 0
                              else (car l) * aux(cdr l)
                in aux l
              catch(x)
                x
    in f [1,2,3,4,5,6,7,8,9,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,8,9]
  )


--- using callcc for looping
  macro p29 = (
   let goto = 0 and n = 0
   in callcc (fun exit -> (
        callcc (fun k -> (& goto := k)) ;   --- "goto _" will jump here
        if n < 100
        then & n := n + 1
        else exit n ;
        goto 0
      ) )
  )

endkm
