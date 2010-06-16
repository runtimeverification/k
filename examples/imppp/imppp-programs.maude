mod IMPPP-PROGRAMS is 
  including IMPPP-SYNTAX .

  ops a b c f i j k m n q s t x y z 
      odd even odd-calls even-calls goto exit : -> Id .
  op p1 : -> AExp .
  eq p1 = 3 + 5 .

  op p2 : -> AExp .
  eq p2 = (3 <= 5) and not (5 <= 1) .

  op p6 : -> Stmt .
  eq p6 = var x ; var y ; y = 1 + ++ y ; print(y) ; .

  op p7 : -> Stmt .
  eq p7 = 
        var n ; var s ; var i ; 
         n = 100 ;
         s = 0 ;
         i = n ;
         while 1 <= i do (
           s = s + i ;
           i = i + -1 ;
          )
          print( s / n ) ; .

  op p13 : -> Stmt .
  eq p13 = var x ; var y ;
           x = 1 ; y = 0 ;
           spawn (x = 0 ;)
           while (1 <= x) do (y = y + 1 ;)
           print(y);
     .

  op p14 : -> Stmt .
  eq p14 = while not(n <= 1) do {
             ++ s ;
             q = n / 2 ;
             if n <= q + q then n = q ; 
             else (n = n + n + n + 1 ;)
           }
        . 
   op p15 : -> Stmt .
   eq p15 = var n ; var s ; var q ;
            s = 0 ;
            n = read ;
            p14
            print s ;
   .
   op p16 : -> Stmt .
   eq p16 = var m ; var n ; var s ; var q ; var i ;
            s = 0 ; m = read ; i = 1 ;
            while (++ i <= m) do {
              n = i ;
              p14
            }
            print s ;
   .
   op p17 : -> Stmt .
   eq p17 = var m ; var s ; var i ; var j ;
            s = 0 ; m = read ; i = 1 ; j = 2 ;
            while (++ i <= m) do {
              var n ; var q ;
              n = i ; 
              spawn (p14 ++ j ;)
            }
            while (j <= m) do {}
            print s ;
   .
endm
