kmod SIMPLE-TYPED-PROGRAMS is including SIMPLE-TYPED-SYNTAX
  syntax Id ::= a | b | c | d | e | f | g | h | i | j | k | l | m | n 
              | o | p | q | r | s | t | u | v | w | x | y | z 
              | main | divide2 | collatz | dummy1 | dummy2 | init 
              | reverse | writeArray | insertionSort | bubbleSort 
              | siftDown | heapSort | map | done | root | bottom | maxChild | size
  syntax Stmts ::= pFactorial | pCollatz | pSorting | pX01


  macro pFactorial =
       var x:int;
       function f(y:int):int {
         var t:int;  var x:bool;
	 t = 1;
         for i = 1 to y do
	   t = t*i;
	 return t;
       }
       function main():void {
         x = 5;
	 write(f(f(x)));
       }


  macro pCollatz =
       var n:int;
       var m:int;

       function divide2(dummy1:int, r:int, dummy2:bool):int {
         var q:int;
	 q = 0;
	 while not r <= 1 do {
	   r = r - 2;
	   q = q + 1;
	 }
	 return q;
       }

       function collatz():int {
         var s:int;
         s = 0;
	 write(n);
         while n > 1 do {
	   s = s+1;
           if n==(n/2)*2
	   then n = divide2(3+n, n, true or false);
	   else n = 3*n+1;
         }
	 return s;
       }

       function main():void {
         m = 10;
         for i = 1 to m do {
	   n = i;
	   write(collatz());
	 }
       }


  macro pSorting =
       function init(n:int):int[] {
         var x[n]:int[];
         for i = 0 to n - 1 do
           x[i] = read();
         return x;
       }

       function writeArray(x:int[]):void {
         for i = 0 to sizeOf(x) - 1 do
           write(x[i]);
       }

       function reverse(x:int[]):void {
         var n:int;
         n = sizeOf(x);
         for i = 0 to n/2 - 1 do {
           var t:int;
           t = x[i];
           x[i] = x[n - i - 1];
           x[n - i - 1] = t;
         }
       }

       function map(f:(int[] -> void)[], x:int[]):void {
         for i = 0 to sizeOf(f) - 1 do {
           f[i](x);
         }
       }

       function insertionSort(x:int[]):void {
         for i = 1 to sizeOf(x) - 1 do {
           var v:int;
           v = x[i];
           var j:int;
           j = i - 1;
           while (j >= 0) do {
             if x[j] > v then
               x[j+1] = x[j];
             j = j - 1;
           }
           x[j+1] = v;
         }
       }

       function bubbleSort(v:int[]):void {
         var n:int;
         n = sizeOf(v);
         for i = 0 to n - 1 do
           for j = 0 to n - 2 do
             if v[j] > v[j+1] then {
               var t:int;
               t = v[j+1];
               v[j+1] = v[j];
               v[j] = t;
             }
       }

       function siftDown(x:int[], root:int, bottom:int):void {
         var done:bool;
         done = false;
         var maxChild:int;
         while (root*2 <= bottom and not done) do {
           if (root*2 == bottom) then {
             maxChild = root*2;
           }
           else if (x[root*2] > x[root*2+1]) then {
                  maxChild = root*2;
                }
	        else {
                  maxChild = root*2+1;
                }
           if (x[root] < x[maxChild]) then {
             var t:int;
             t = x[root];
             x[root] = x[maxChild];
             x[maxChild] = t;
             root = maxChild;
           }
           else {
             done = true;
           }
         }
       }

       function heapSort(x:int[]):void {
         var n:int;
         n = sizeOf(x);
         var i:int;
         i = n / 2 - 1;
         while (i >= 0) do {
           siftDown(x, i, n - 1);
           i = i - 1;
         }
         i = n - 1;
         while (i>=1 ) do {
           var t:int;
           t = x[0];
           x[0] = x[i];
           x[i] = t;
           siftDown(x, 0, i - 1);
           i = i - 1;
         }
       }

       function main():void {
         var x:int[];
         var n:int;
         x = init(read());
         var f[11]:(int[]->void)[];
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
 

--- the following program passes the type system
--- to check such anomalies the system should manage the environment
---   structured as a stack of layers, similar to object environments  
---   and to write a function gettype similar to getloc from SKOOL

  macro pX01 =
       var x:int;
       function f():int {
          return x;
       }
       var x:bool;
       function f():bool {
          return x;
       }
       function main():void {
          x = f();
       }
endkm
