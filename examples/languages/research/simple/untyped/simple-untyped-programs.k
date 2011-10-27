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
