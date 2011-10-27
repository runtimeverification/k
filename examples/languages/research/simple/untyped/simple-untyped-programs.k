-------------------------------------------------------------------
--- Lots of SIMPLE programs to be used first to test the syntax ---
--- and then to test the semantics.                             ---
-------------------------------------------------------------------

kmod SIMPLE-UNTYPED-PROGRAMS is including SIMPLE-UNTYPED-SYNTAX
  syntax #Id ::= a | b | c | d | e | f | g | h | i | j | k | l | m 
              | n | o | p | q | r | s | t | u | v | w | x | y | z 
              | main | divide2 | collatz | dummy1 | dummy2 | init | reverse 
              | printAll | writeArray | insertionSort | bubbleSort | siftDown 
              | heapSort | map | done | root | bottom | maxChild | temp
              | numbers | size | readArray | printArray | mulArray | transArray

  syntax Stmts ::= pFactorial | pCollatz | pInsertionSort1 | pInsertionSort2
                 | pInsertionSort3 | pInsertionSort4 | pBubbleSort
                 | pHeapSort | pSorting | pex01 | pArrays  

	

  macro pArrays =
       function readArray(a) {
         var m = sizeOf(a) - 1, n = sizeOf(a[0]) - 1;
         for i = 0 to m do
           for j = 0 to n do a[i][j]=read();
       }

       function printArray(a) {
         var m = sizeOf(a) - 1, n = sizeOf(a[0]) - 1;
         for i = 0 to m do
           for j = 0 to n do write(a[i,j]);
       }

       function transArray(a) {
         var  m = sizeOf(a) - 1,  n = sizeOf(a[0]) - 1, b[n+1,m+1];
         for i = 0 to m do
           for j = 0 to n do
             b[j,i]=a[i,j];
         return b;
       }

       function mulArray(a,b) {
         var m=sizeOf(a) - 1, n=sizeOf(b) - 1, p=sizeOf(b[0]) - 1, c[m+1,p+1];
         for i=0 to m do for j=0 to p do {
           c[i,j]=0;
           for k=0 to n do
             c[i,j]=c[i,j]+a[i,k]*b[k,j];
         }
         return c;
       }

       function main() {
         var x = read(), y = read(), a[x,y];
         readArray(a);
         printArray(mulArray(a,transArray(a)));
       }


--- programs to test exceptions

  syntax Stmts ::= pExceptions1
  macro pExceptions1 =
       function main() {
         var e = 100;
         try {
           var x = 5;
           if (x >= 0) then throw x+2;
           write(20);  --- should not be written
         } catch(e) {
           write(e);   --- should write 7
         }
         write(e);     --- should write 100
         write(10);
       }
--- 7 100 10


  syntax #Id ::= foo
  syntax Stmts ::= pExceptions2
  macro pExceptions2 =
    function main() {
      try
        foo();
      catch(e)
        write(e);  --- should write 7
    }

    function foo() {
      try {
        throw 5;
        write(7);  --- should not be written
      } catch(e) {
        throw e+2; --- throws 7
      }
      throw 1;     --- should not be reached
    }
--- 7


  syntax Stmts ::= pExceptions3
  macro pExceptions3 =
    function main() {
      var x = 1;
      try { x = x + 1; throw x; var y = x/0;}     --- division by zero unreachable
      catch(y) {x = x+1;}
      write(x);
    }
--- 3


  syntax Stmts ::= pExceptions4
  macro pExceptions4 =
    function main() {
      var x = 1;
      try { var x = 5; throw x; var y = x/0;}  --- division by zero unreachable
      catch(y) {y = y + 2; write(y);}                --- new y here, the one declared by catch
      write(x);
    }
--- 7 1


  syntax Stmts ::= pExceptions5
  macro pExceptions5 =
    var x;

    function f(y) {
      var t = 1;
      try{
        write(t);
        throw 5;
        write(8);  --- not reachable
      } catch(p) {
        write(p+10);
      }
      for i = 1 to y do
        t = t*i;
      return t;
    }

    function main() {
      x = 5;
      write(f(x));
    }
--- 1 15 120


  syntax Stmts ::= pExceptions6
  macro pExceptions6 =
    var x;

    function f(y) {
      var t = 1;
      try{
        write(t);
        write(8);
      } catch(p) {
        write(p+10);  --- not reachable
      }
      for i = 1 to y do
        t = t*i;
      return t;
    }

    function main() {
      x = 5;
      write(f(x));
    }
--- 1 8 120


  syntax Stmts ::= pExceptions7
  macro pExceptions7 =
    function main() {
      var e;
      try { var x = 2; write(x); throw ( ++x + x ); }
      catch(e) { write(e); }
    }
--- 2 6 or 2 5


  syntax Stmts ::= pExceptions8
  macro pExceptions8 =
   function main() {
     var e;
     try {
       try {
         try {
           try {
             var x = 1; write(x); throw ++x;
           } catch(e) {
             write(e);
             throw ++e;
           }
         } catch(e) {
           write(e);
           throw ++e;
         }
       } catch(e) {
         write(e);
         throw ++e;
       }
     } catch(e) {
       write(e);
     }
   }
--- 1 2 3 4 5


  syntax Stmts ::= pExceptions9
  macro pExceptions9 =
    var x, y, z;

    function g() {
      throw 15;
    }

    function f() {
      g();
    }

    function main() {
      x = 5;
      y = 10;

      try {
        f();
      } catch(y) {
        write(y);
      }
      write(x);
      write(y);
    }
--- 15 5 10


  syntax Stmts ::= pExceptions10
  macro pExceptions10 =
    var x;

    function main() {
      x = 5;
      try {
        throw 3;
        write(x);
      } catch(y) {
        write(y);
      }
    }
--- 3


  syntax Stmts ::= pExceptions11
  macro pExceptions11 =
    var i, j = 0;

    function main() {
      i = 0;
      while (++i <= 3) do {
        write(i);
      }
      try ({throw j; i = 10; write(i);}) catch(j) ({i = 20;write(i);})
      i = 15;
      write(i);
    }
--- 1 2 3 20 15


  syntax Stmts ::= pExceptions12
  macro pExceptions12 =
    var i, j;

    function main() {
      i = 0;
      while (++i <= 3) do {
        write(i);
      }
      try ({i = 10; write(i);}) catch(j) ({i = 20;write(i);})
      i = 15;
      write(i);
     }
--- 1 2 3 10 15


  syntax Stmts ::= pExceptions13
  macro pExceptions13 =
    function main() {
      try {
        throw 4;
      } catch (e) {
        write ( e );
      }
      write ( 42 );
    }
--- 4 42


  syntax Stmts ::= pExceptions14
  macro pExceptions14 =
    function main() {
      try {
        15;
      } catch ( e ) {
        write ( e );
      }
      write ( 42 );
    }
--- 42


  syntax Stmts ::= pExceptions15
  macro pExceptions15 =
    function main() {
      try {
        1;
        try {
          2;
        } catch(a) {
          write(2);
        }
        throw 1;
      } catch(b) {
        write(1);
      }
    }
--- 1


--- programs to test non-deterministic evaluation

  syntax Stmts ::= pNondet
  macro pNondet =
    var x;
    function main() {
      x = 1 ;
      x = ++ x / (++ x / x);
      write(x);
}
--- 0
--- 1
--- 2
--- 3
--- undefined (gets stuck with division-by-zero at top of computation)


--- programs to test dynamic threads and synchronization

  syntax #Id ::= factorialOf | multX
  syntax Stmts ::= pThreads1
  macro pThreads1 =
    var x;
    function main() {
      var factorialOf = 5;
      x = 1;
      for i = 1 to factorialOf do {
        spawn multX(i);
      }
      for i = 1 to factorialOf do
        rendezvous i;
      write(x);
    }
    function multX(v) {
      acquire 0;
      x = x*v;
      release 0;
      rendezvous v;
    }
--- 120
--- only execute, do not search; too slow


  syntax Stmts ::= pThreads2
  macro pThreads2 =
    function main() {
      var x = 5;
      spawn x=x+2;
      spawn x=x*2;
      spawn x=11;
      spawn write(x);
    }
--- there are 42 solutions


  syntax Stmts ::= pThreads3
  macro pThreads3 =
    function main() {
      var x = 1;
      spawn {rendezvous 1; write(x); rendezvous 2;}
      spawn {rendezvous 3; write(x); rendezvous 4;}
      write(x);
      x = x+1;
      rendezvous 1;  rendezvous 2;
      x = x+1;
      rendezvous 3; rendezvous 4;
    }
--- 1 2 3


  syntax Stmts ::= pThreads4
  macro pThreads4 =
    function main() {
      var x = 1;
      spawn {x = x+1; rendezvous 1;}
      x = x+1;
      rendezvous 1;
      write(x);
    }
--- 2
--- 3


  syntax Stmts ::= pThreads5
  macro pThreads5 =
    function main() {
      var x = 1;
      spawn {acquire 1; x = x+1; release 1; rendezvous 1;}
      acquire 1;
       x = x+1;
      release 1;
      rendezvous 1;
      write(x);
    }
--- 3


  syntax Stmts ::= pThreads6
  macro pThreads6 =
   function main() {
     spawn {
       var e;
       try {
         try {
           try {
             try {
               var x = 1; write(x); throw ++x;
             } catch(e) {
               write(e);
               throw ++e;
             }
           } catch(e) {
             write(e);
             throw ++e;
           }
         } catch(e) {
           write(e);
           throw ++e;
         }
       } catch(e) {
         write(e);
       }
     }
     spawn {
       var e;
       try {
         try {
           try {
             try {
               var x = 1; write(x); throw ++x;
             } catch(e) {
               write(e);
               throw ++e;
             }
           } catch(e) {
             write(e);
             throw ++e;
           }
         } catch(e) {
           write(e);
           throw ++e;
         }
       } catch(e) {
         write(e);
       }
     }
   }
--- 221 solutions, outputing each two 1, two 2, two 3, two 4 and two 5


  syntax Stmts ::= pThreads7
  macro pThreads7 =
    var x, y;

    function main() {
      x = 1;
      y = 0;
      spawn x = 0;
      while (1 <= x) do { y = y+1; }
      write(y);
    }
--- infinitely many solutions; search should list them until stopped


  syntax Stmts ::= pThreads8
  macro pThreads8 =
    function main() {
      var x = 5;
      spawn x = 7;
      write ( x );
    }
--- 5
--- 7


  syntax Stmts ::= pThreads9
  macro pThreads9 =
    function main() {
      var x;
      spawn x = 7;
      x = 5;
      write ( x );
    }
--- 5
--- 5 (yes, it admits two behaviors where the output is 5)
--- 7


  syntax Stmts ::= pThreads10
  macro pThreads10 =
    function main() {
      spawn { var x = 2; write(x); }
      spawn { var x = 3; write(x); }
    }
--- 2 3
--- 3 2


--- Dekker's algorithm; not meant to be executed, but only model checked
  syntax #Id ::= task1 | task2 | dekker1 | dekker2 | flag1 | flag2
              | critical1 | critical2 | turn
  syntax Stmts ::= pDekker
  macro pDekker =
       var flag1 = 0, flag2 = 0, turn = 1, critical1 = 0, critical2 = 0;

       function dekker1() {
         flag1 = 1; turn = 2;
         while((flag2 == 1) and (turn == 2)) do { }

         // Enter critical section
         critical1 = 1;
         // Critical stuff ...
         // Leave critical section
         critical1 = 0;

         flag1 = 0;
       }

       function dekker2() {
         flag2 = 1; turn = 1;
         while((flag1 == 1) and (turn == 1)) do { }

         // Enter critical section
         critical2 = 1;
         // Critical stuff ...
         // Leave critical section
         critical2 = 0;

         flag2 = 0;
       }

       function main() {
         spawn while(true) do { dekker1(); }
         spawn while(true) do { dekker2(); }
       }

endkm
