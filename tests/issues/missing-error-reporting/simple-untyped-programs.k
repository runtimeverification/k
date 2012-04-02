-------------------------------------------------------------------
--- Lots of SIMPLE programs to be used first to test the syntax ---
--- and then to test the semantics.                             ---
-------------------------------------------------------------------

kmod SIMPLE-UNTYPED-PROGRAMS is including SIMPLE-UNTYPED-SYNTAX
  syntax Id ::= a | b | c | d | e | f | g | h | i | j | k | l | m 
              | n | o | p | q | r | s | t | u | v | w | x | y | z 
              | main | divide2 | collatz | dummy1 | dummy2 | init | reverse 
              | printAll | writeArray | insertionSort | bubbleSort | siftDown 
              | heapSort | map | done | root | bottom | maxChild | temp
              | numbers | size | readArray | printArray | mulArray | transArray

  syntax Stmts ::= pFactorial | pCollatz | pInsertionSort1 | pInsertionSort2
                 | pInsertionSort3 | pInsertionSort4 | pBubbleSort
                 | pHeapSort | pSorting | pex01 | pArrays  

	
  macro pFactorial =
       var x;

       function f(y) {
         var t=1;
         for i = 1 to y do
	   t = t*i;
	 return t;
       }

       function main() {
         x = 5;
	 write(f(f(x)));
       }


  macro pCollatz =
       var n, m;

       function divide2(dummy1, r, dummy2) {
         var q=0;
	 while not r <= 1 do {
	   r = r - 2;
	   q = q + 1;
	 }
	 return q;
       }

       function collatz() {
         var s=0;
	 write(n);
         while n > 1 do {
	   s = s+1;
           if n == (n/2)*2
	   then n = divide2(3+n, n, true or false);
	   else n = 3*n+1;
         }
	 return s;
       }

       function main() {
         m = 10;
         for i = 1 to m do {
	   n = i;
	   write(collatz());
	 }
       }


--- following does not run, because "and" is not shortcut in SIMPLE (though it types)
  macro pInsertionSort1 =
       var x[10];

       function init(n) {
         for i = 0 to n - 1 do
           x[i] = (n - i) + 100;
       }

       function printAll(n) {
         for i = 0 to n - 1 do
           write(x[i]);
       }

       function main() {
         var n=10;
         init(n);
         printAll(n);
         for i = 1 to n - 1 do {
           var j=i - 1, v=x[i];
           while (j >= 0 and ((x[j]) > v)) do {
             x[j + 1] = x[j];
             j = j - 1;
           }
           x[j+1] = v;
         }
         printAll(n);
       }


  macro pInsertionSort2 =
       var x[100];

       function init(n) {
         for i = 0 to n - 1 do
           x[i] = (n - i) + 100;
       }

       function printAll(n) {
         for i = 0 to n - 1 do
           write(x[i]);
       }

       function main() {
         var n = 30;
         init(n);
         printAll(n);
         write(-1);
         for i = 1 to n - 1 do {
           var j = i - 1, v = x[i];
           while (j >= 0) do {
             if x[j] > v then x[j+1] = x[j];
             j = j - 1;
           }
           x[j+1] = v ;
         }
         printAll(n);
       }


  macro pInsertionSort3 =
       function init(x,n) {
         for i = 0 to n - 1 do
           x[i] = (n-i) + 100;
       }

       function printAll(x,n) {
         for i = 0 to n - 1 do
           write(x[i]);
       }

       function main() {
         var x[100], n = 30;
         init(x,n);
         printAll(x,n);
         write(-1);
         for i = 1 to n - 1 do {
           var j = i - 1, v = x[i];
           while (j >= 0) do {
             if x[j] > v then x[j+1] = x[j];
             j = j - 1;
           }
           x[j+1] = v;
         }
         printAll(x,n);
       }


  macro pInsertionSort4 =
       function init(n) {
         var x[100];
         for i = 0 to n - 1 do
           x[i] = (n-i) + 100;
         return x;
       }

       function printAll(x,n) {
         for i = 0 to n - 1 do
           write(x[i]);
       }

       function main() {
         var n = 30, x = init(n);
         printAll(x,n);
         write(-1);
         for i = 1 to n - 1 do {
           var j = i - 1, v = x[i];
           while (j >= 0) do {
             if x[j] > v then x[j+1] = x[j];
             j = j - 1;
           }
           x[j+1] = v;
         }
         printAll(x,n);
       }


  macro pBubbleSort =
       var v[100];

       function bubbleSort(n) {
         var t;
         for x = 0 to n - 1 do
           for y = 0 to n - 2 do
             if v[y] > v[y+1] then {
               t = v[y+1];
               v[y+1] = v[y];
               v[y] = t;
             }
       }

       function main() {
         var x = read();
         for y = 0 to (x - 1) do {
	   v[y] = read();
	   write(v[y]);
	 }
         bubbleSort(x);
         for y = 0 to (x - 1) do
	   write(v[y]);
       }



  macro pHeapSort =
       var numbers[100];

       function siftDown(root, bottom) {
         var done = false, maxChild, temp;

         while (root*2 <= bottom and not done) do {
           if (root*2 == bottom) then {
             maxChild = root*2;
           }
           else if (numbers[root*2] > numbers[root*2 + 1]) then {
                  maxChild = root*2;
                }
                else { maxChild = root*2 + 1; }
           if (numbers[root] < numbers[maxChild]) then {
             temp = numbers[root];
             numbers[root] = numbers[maxChild];
             numbers[maxChild] = temp;
             root = maxChild;
           }
           else {done = true;}
         }
       }

      function heapSort(size){
        var temp, i = (size/2) - 1;
        while (i >= 0) do {
          siftDown(i, size - 1);
          i = i - 1;
        }
        i = size - 1;
        while (i >= 1 ) do {
          temp = numbers[0];
          numbers[0] = numbers[i];
          numbers[i] = temp;
          siftDown(0, i - 1);
          i = i - 1;
        }
      }

      function main() {
        var x = read() ;
        for i = 0 to (x - 1) do {
          numbers[i] = read();
        }
        heapSort(x) ;
        for i = 0 to (x - 1) do {
          write(numbers[i]);
        }
      }


  macro pSorting =
       function init(n) {
         var x[n];
         for i = 0 to n - 1 do
           x[i] = i;
         return x;
       }

       function writeArray(x) {
         for i = 0 to sizeOf(x) - 1 do
           write(x[i]);
       }

       function reverse(x) {
         var n = sizeOf(x);
         for i = 0 to n/2 - 1 do {
           var t = x[i];
           x[i] = x[n - i - 1];
           x[n - i - 1] = t;
         }
       }

       function map(f,x) {
         for i = 0 to sizeOf(f) - 1 do {
           f[i](x);
         }
       }

       function insertionSort(x) {
         for i = 1 to sizeOf(x) - 1 do {
           var v = x[i], j = i - 1;
           while (j >= 0) do {
             if x[j] > v then
               x[j+1] = x[j];
             j = j - 1;
           }
           x[j+1] = v;
         }
       }

       function bubbleSort(v) {
         var n = sizeOf(v);
         for i = 0 to n - 1 do
           for j = 0 to n - 2 do
             if v[j] > v[j+1] then {
               var t = v[j+1];
               v[j+1] = v[j];
               v[j] = t;
             }
       }

       function siftDown(x, root, bottom) {
         var done = false, maxChild;
         while (root*2 <= bottom and not done) do {
           if (root*2 == bottom) then {
             maxChild = root*2;
           }
           else if (x[root*2] > x[root*2 + 1]) then {
                  maxChild = root*2;
                }
	        else {
                  maxChild = root*2 + 1;
                }
           if (x[root] < x[maxChild]) then {
             var t = x[root];
             x[root] = x[maxChild];
             x[maxChild] = t;
             root = maxChild;
           }
           else {
             done = true;
           }
         }
       }

       function heapSort(x){
         var n = sizeOf(x), i = n/2 - 1;
         while (i >= 0) do {
           siftDown(x, i, n - 1);
           i = i - 1;
         }
         i = n - 1;
         while (i >= 1 ) do {
           var t = x[0];
           x[0] = x[i] ;
           x[i] = t;
           siftDown(x, 0, i - 1);
           i = i - 1;
         }
       }

       function main() {
         var n = 10, x = init(n), f[11];
         f[ 0] = writeArray;
         f[ 1] = reverse;
         f[ 2] = writeArray;
         f[ 3] = insertionSort;
         f[ 4] = writeArray;
         f[ 5] = reverse;
         f[ 6] = bubbleSort;
         f[ 7] = writeArray;
         f[ 8] = reverse;
         f[ 9] = heapSort;
         f[10] = writeArray;
         map(f,x);
       }


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


  syntax Id ::= foo
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

  syntax Id ::= factorialOf | multX
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
  syntax Id ::= task1 | task2 | dekker1 | dekker2 | flag1 | flag2
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
