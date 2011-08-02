kmod EXP-PROGRAMS is including EXP-SYNTAX
  syntax #Id ::= a | b | c | d | e | f | g | h | i | j | k
              | l | m | n | o | p | q | r | s | t | u | v | w | x | y | z
              | f00 | f01 | f02 | f03 | f04 | f05 | f06 | f07 | f08 | f09 | f10 | f11 | f12 | f13 | f14

  syntax Exp ::= p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 | p12 | p13 | p14 | p15 | p16 | p17


  macro p1 = (
    letrec f x = if x <= 0 then 1 else x * f(x - 1)
    in f (f 5)
  )

  macro p2 = (
    let x = 1
    in let f = lambda a . x
       in let x = true
          in f 3
  )
  
  macro p3 = (
    let f = lambda x . x
    in f 1
  )

  macro p4 = (
    lambda x . (x x)
  )

  macro p5 = (
    let f = lambda x . x
    in if f true then f 3 else f 4 
  )

  macro p6 = (
    letrec f x = 3
    in f
  )
  
  macro p7 = (
    let f = let g = lambda x . x
            in let h = lambda x . lambda y . (g g)
	       in h
    in f
  )

  macro p8 = (
    let f = lambda x . x
    in f f
  )

  macro p9 = (
    let f00 = lambda x . lambda y . x in
      let f01 = lambda x . f00 (f00 x) in
        let f02 = lambda x . f01 (f01 x) in
---          let f03 = lambda x . f02 (f02 x) in
---            let f04 = lambda x . f03 (f03 x) in
---              let f05 = lambda x . f04 (f04 x) in
---                let f06 = lambda x . f05 (f05 x) in
---                  let f07 = lambda x . f06 (f06 x) in
---                    let f08 = lambda x . f07 (f07 x) in
---                      let f09 = lambda x . f08 (f08 x) in
---                        let f10 = lambda x . f09 (f09 x) in
---                          let f11 = lambda x . f10 (f10 x) in
                            f02
  )

  macro p10 = (
    letrec f x = if x < 1 then 0 else f(x - 1) + 1
    in f 100
  )

  macro p11 = (
    (lambda z . z z)(lambda x . lambda y . x y)
  )

--- this program tests that the fix point uses its own closure
  macro p12 = (
    let y = 0
    in letrec f x = if x == 0 then y else let y = 1 in f(x - 1)
       in f 1
  )

  macro p13 = (
    lambda x .
      let f = lambda y . if true then y else x
      in lambda x . f 0
  )

  macro p14 = (
    lambda x . let f = lambda y . if true then x 7 else x y
               in f
  )

  macro p15 = (
    lambda x . let f = lambda x . x
               in let d = (f x) + 1
                  in x
  )

  macro p16 = (
    lambda x . let f = lambda y . x y
               in let z = x 0 in f
  )

--- this tests that one does not use the unifying substitution to find the type parameters
  macro p17 = (
    let f = lambda x . x in
      let g = lambda y . f y in
        g g
  )
endkm
