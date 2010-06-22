--- in skool-untyped-syntax

kmod SKOOL-UNTYPED-PROGRAMS is including SKOOL-UNTYPED-SYNTAX

  syntax Id ::= 
                a | b | c 
              | d | e | f 
              | g | h | i 
              | j | k | l 
              | m | n | o 
              | p | q | r 
              | s | t | u 
              | v | w | x 
              | y | z 
              | m1 | m2 | m3
              | divide2 | collatz 
              | dummy1 | dummy2 | init 
              | reverse | printAll 
              | writeArray | insertionSort
              | bubbleSort | siftDown 
              | heapSort | map | done 
              | root | bottom | maxChild 
              | temp | numbers | size
              | odd | even | oddeven
              | node | left | right
              | sum | leaf | value 
              | point | move | writeLocation
              | initx | inity | initcolor 
              | dx | dy | colorpoint 
              | color | setColor | writeColor
              | cp | c1 | c2
              | c3 | o1 | o2
              | o3 | setx1 | setx2
              | getx1 | getx2 | sety1
              | sety2 | gety1 | gety2
              | setup | do | obj
              | get | sorting | input 
              | array | init | read2
              | done | root | bottom
              | maxChild | test | add
              | write2

  syntax Stmts ::= 
                pFactorial | pCollatz 
              | pInsertionSort1 | pInsertionSort2 
              | pInsertionSort3 | pInsertionSort4 
              | pBubbleSort | pHeapSort 
              | pSorting

  syntax ClassDecl ::= 
                p01 | p02 | p03 
              | p04 | p05 | p06 
              | p07 | p08 | p09 
              | p10 | p11 | p12 
              | p13 | p14 | p15 
              | p16 | p17 | p18 
              | p19 | p20 
  
  macro p01 =
       class main {
         var a;
         method main() {
           a = 1;
           write(a);
           return 0;
         }
       }

  macro p02 =
       class c {
         var a;
         method c() { a = 5; return 0; }
         method g() { return a; }
       }
       class main {
         method main() {
           write((new c()).g());
	   return 0;
         }
       }

  macro p03 =
       class c {
         var i;
         var j;
         method c(x) {
           i = x;
           j = ++x;
	   return 0;
         }
         method add(d) {
           i = i+d;
           j = j-d;
	   return 0;
         }
         method write2() {
           write(i);
           write(j);
	   return 0;
         }
       }

       class main {
         var a;
         var b;
         var o;
         method main(){
           a = 0; b = 0; o = new c(5);
           o.write2();
           o.add(3);
           o.write2();
	   return 0;
         }
       }


endkm

