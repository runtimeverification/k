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
              | write2 | val

  syntax Stmts ::= 
                pFactorial | pCollatz 
              | pInsertionSort1 | pInsertionSort2 
              | pInsertionSort3 | pInsertionSort4 
              | pBubbleSort | pHeapSort 
              | pSorting

  syntax Stmts ::= 
                p01 | p02 | p03 
              | p04 | p05 | p06 
              | p07 | p08 | p09 
              | p10 | p11 | p12 
              | p13 | p14 | p15 
              | p16 | p17 | p18 
              | p19 | p20 | p21
              | p22
  
  macro p01 =
       class main {
         var a;
         method main() {
           a = 1;
           write(a);
           return 0;
         }
       }

--- 1

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

--- 5

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

--- 5 6 8 3

  macro p04 =
       class c {
         method c() { return 0; }
         method m1() {
	   return this.m2();
	 }
         method m2() {
	   return 13;
	 }
       }
       class main {
         method main() {
           write((new c()).m1());
	   return 0;
         }
       }

--- 13

  macro p05 =
       class oddeven {
         var n;
         method oddeven(x) { n = x; return 0; }
         method even() {
           if n == 0 then return 1; else { n = n - 1; return this.odd(); }
         }
         method odd() {
           if n == 0 then return 0;else { n = n - 1; return this.even(); }
         }
       }
       class main {
         method main() {
           write((new oddeven(17)).odd());
           return 0;
         }
       }

--- 1

  macro p06 =
       class node {
         var left;
         var right;
         method node(l,r) {
           left = l;
           right = r;
           return 0;
         }
         method sum() {
          return (left.sum() + right.sum());
         }
       }
       class leaf {
         var value;
         method leaf(v) {
           value = v;
           return 0;
         }
         method sum() {
           return value;
         }
       }
       class main {
         method main() {
           var o;
           o = new node(new node(new leaf(3), new leaf(4)), new leaf(5));
           write(o.sum());
           return 0;
         }
       }

--- 12

  macro p07 =
       class point {
         var x;
         var y;
         method point(initx, inity) {
           x = initx;
           y = inity;
           return 0;
         }
         method move(dx, dy) {
           x = x+dx;
           y = y+dy;
           return 0;
         }
         method writeLocation() {
           write(x);
           write(y);
           return 0;
         }
       }
       class colorpoint extends point {
         var color;
	 method colorpoint(initx, inity) {
           x = initx;
           y = inity;
           return 0;
         }
         method setColor(c) {
           color = c;
	   return 0;
         }
         method writeColor() {
           write(color);
           return 0;
         }
       }
       class main {
         method main() {
           var p;
           var cp;
           p = new point(3,4);
           cp = new colorpoint(10,20);
           p.move(3,4);
           p.writeLocation();
           cp.setColor(87);
           cp.move(10, 20);
           cp.writeLocation();
           cp.writeColor();
           return 0;
         }
       }

--- 6 8 20 40 87

  macro p08 =
       class point {
         var x;
         var y;
         method point(initx, inity) {
           x = initx;
           y = inity;
           return 0;
         }
         method move(dx, dy) {
           x = x + dx;
           y = y + dy;
	   return 0;
         }
         method writeLocation() {
           write(x);
           write(y);
	   return 0;
         }
       }
       class colorpoint extends point {
         var color;
         method colorpoint(initx,inity,initcolor) {
           x = initx;
           y = inity;
           color = initcolor;
           return 0;
         }
         method setColor(c) {
           color = c;
           return 0;
         }
         method writeColor() {
           write(color);
           return 0;
         }
       }
       class main {
         method main() {
           var p;
           var cp;
           p = new point(3,4);
           cp = new colorpoint(10,20,87);
           p.move(3,4);
           cp.move(10,20);
           p.writeLocation();
           cp.writeLocation();
           cp.writeColor();
           return 0;
        }
      }

--- 6 8 20 40 87

  macro p09 =
       class point {
         var x;
         var y;
         method point(initx, inity) {
           x = initx;
           y = inity;
           return 0;
         }
         method move(dx, dy) {
           x = x + dx;
           y = y + dy;
	   return 0;
         }
         method writeLocation() {
           write(x);
           write(y);
	   return 0;
         }
       }
       class colorpoint extends point {
         var color;
         method colorpoint(initx,inity,initcolor) {
           this.point(initx, inity);
           color = initcolor;
           return 0;
         }
         method setColor(c) {
           color = c;
           return 0;
         }
         method writeColor() {
           write(color);
           return 0;
         }
       }
       class main {
         method main() {
           var p;
           var cp;
           p = new point(3,4);
           cp = new colorpoint(10,20,87);
           p.move(3,4);
           cp.move(10,20);
           p.writeLocation();
           cp.writeLocation();
           cp.writeColor();
           return 0;
        }
      }
 
--- 6 8 20 40 87

  macro p10 = 
       class c1 {
         var x;
         var y;
	 method c1() { return 0;}
         method setx1(v) { x = v; return 0;}
         method sety1(v) { y = v; return 0;}
         method getx1() { return x; }
         method gety1() { return y; }
       }
       class c2 extends c1 {
         var y;
	 method c2() { return 0;}
         method sety2(v) { y = v; return 0;}
         method getx2() { return x; }
         method gety2() { return y; }
       }
       class main {
         method main() {
           var o2;
           o2 = new c2();
           o2.setx1(11);
           o2.sety1(12); 
           o2.sety2(99);
           write(o2.getx1());
           write(o2.gety1());
           write(o2.getx2());
           write(o2.gety2());
           return 0;
         }
       }

--- 11 12 11  99

  macro p11 =
       class c1 {
         method c1() { return 0;}
         method m1() { return 1; }
         method m2() { return this.m1(); }
       }
       class c2 extends c1 {
         method c2() { return 0;}
         method m1() { return 2; }
       }
       class main {
         method main() {
           var o1;
           var o2;
           o1 = new c1();
           o2 = new c2();
           write(o1.m1());
           write(o2.m1());
           write(o2.m2());
           return 0;
         }
       }

--- 1 2 2 

  macro p12 =
       class c1 {
         method c1() { return 0; }
         method m1() { return 1; }
         method m2() { return 100; }
         method m3() { return this.m2(); }
       }
       class c2 extends c1 {
         method c2() { return 0; }
         method m2() { return 2; }
       }
       class main {
         method main() {
           var o1;
           var o2;
           o1 = new c1();
           o2 = new c2();
           write(o1.m1());
           write(o1.m2());
           write(o1.m3());
           write(o2.m1());
           write(o2.m2());
           write(o2.m3());
           return 0;
         }
       }

--- 1 100 100 1 2 2 

  macro p13 =
       class c1 {
         method c1() { return 0; }
         method m1() {
           return(this.m2());
         }
         method m2() { return 13; }
       }
       class c2 extends c1 {
         method c2() { return 0;}
         method m1() { return 22; }
         method m2() { return 23; }
         method m3() {
           return(super m1());
         }
       }
       class c3 extends c2 {
         method c3() { return 0; }
         method m1() { return 32; }
         method m2() { return 33; }
       }
       class main {
         method main() {
           var o3;
           o3 = new c3();
           write(o3.m3());
           return 0;
         }
       }

--- 33 

  macro p14 =
       class a {
         var i;
         var j;
         method a() {
           i = 1;
           j = i + 1;
	   return j;
	 }
	 method f() {
	   return this.a();
	 }
         method g() {
           return this.f();
         }
         method h() {
	   return (i + j);
	 }
       }
       class b extends a {
         var j;
         var k;
	 method a() {
	   return this.b();
	 }
         method b() {
	   super a();
           j = 10;
           k = j + 1;
	   return k;
	 }
	 method g() {
	   return super h();
	 }
	 method h() {
	   return this.g();	   
	 }
       }
       class c extends b {
         method a() {
	   return super a();
	 }
	 method b() {
	   return super b();
	 }
         method c() {
	   i = 100;
	   j = i + 1;
	   k = j + 1;
	   return k;
	 }
         method g() {
           return (i + k * j);
         }
       }
       class main {
         method p(o) {
           write(o.f());
           write(o.g());
           write(o.h());
           return 0;
         }
         method main() {
           this.p(new a());
           this.p(new b());
           this.p(new c());
           return 0;
         }
       }

--- 2 2 3 11 3 3 102 10402 10402  ???

--- 2 2 3 11 3 3 11 111 111 

  macro p15 =
       class i {
         var value;
         method i(v) {
           value = v;
           return 0;
         }
         method m1() {
           return (new g(value + 9));
         }
       }
       class g {
         var a;
         method g(t) {
           a = t;
           return 0;
         }
         method write2() { write(a); return 0; }
       }
       class main {
         method main() {
           ((new i(1)).m1()).write2();
           return 0;
         }
       }

--- 15 ???
--- 10

  macro p16 =
       class i {
         var f;
         method i(v) {
           f = v;
           return 0;
         }
         method get() { return f; }
       }
       class g {
         var o;
         method g(obj) {
           o = obj;
           return 0;
         }
         method do() {
           var f;
           f = 9;
           return (o.get());
         }
       }
       class main {
         method main() {
           var t;
           var y;
           t = new i(1);
           y = new g(t);
           write(y.do());
           return 0;
         }
       }

--- 1

  macro p17 =
       class main {
	 method f(x) {
	   if x <= 1 then return 1; else return(x * (this.f(x - 1)));
	 }
	 method main() {
	   write(this.f(this.f(5)));
	   return 0;
         }
       }

--- (5!)!

  macro p18 =
       class sorting {
         var input[100];
         var array[100];
         var n;
 
         method sorting(x) {
           n = x;
           return 0;
         }

         method read2() {
           for i = 0 to (n - 1) do {
             input[i] = read();
           }
           return 0;
         }

         method init() {
           for i = 0 to (n - 1) do
             array[i] = input[i];
           return 0;
         }
 
         method write2() {
           for i = 0 to (n - 1) do
             write(array[i]);
           return 0;
         }

         method insertionSort() {
            for i = 1 to n - 1 do {
              var j;
              var done;
              var t;
              t = array[i];
              done = false;
              j = i - 1;
              while (j >= 0) and not done do
                if array[j] > t
                then {
                  array[j+1] = array[j];
                  j = j - 1;
                }
                else done = true;
              array[j + 1] = t;
            }
           return 0;
         }

         method bubbleSort() {
           var t;
           for i = 0 to n - 1 do
             for j = 0 to n - 2 do
               if array[j] > array[j+1] then {
                 t = array[j+1];
                 array[j+1] = array[j];
                 array[j] = t;
               }
           return 0;
         }

         method siftDown(root, bottom) {
             var done;
             var maxChild;
             var t;
             done = false;
       
             while (root*2 <= bottom and not done) do {
                if (root*2 == bottom) then {
                  maxChild = root * 2;
                }
                else if (array[root * 2] > array[root * 2 + 1]) then {
                       maxChild = root * 2;
                     }
                     else { maxChild = root * 2 + 1; }
                if (array[root] < array[maxChild]) then {
                  t = array[root];
                  array[root] = array[maxChild];
                  array[maxChild] = t;
                  root = maxChild;
                }
                else { done = true; }
             }
           return 0;
         }

         method heapSort(){
           var t;
           var i;
           i = (n/2) - 1;
           while (i >= 0) do {
             this.siftDown(i, n - 1);
             i = i - 1;
           }
           i = n - 1;
           while (i >= 1 ) do {
             t = array[0];
             array[0] = array[i];
             array[i] = t;
             this.siftDown(0, i - 1);
             i = i - 1;
           }
           return 0;
         }
       }

       class main {
         method main() {
           var s;
           s = new sorting(read());
           s.read2();

           s.init();
           s.insertionSort();
           s.write2();

           write(-1);

           s.init();
           s.bubbleSort();
           s.write2();

           write(-1);

           s.init();
           s.heapSort();
           s.write2();

           return 0;
         }
       }

  
  macro p19 =
       class c {
         method c() { return 0; }
         method test() {
	   write(-1);
           if this instanceOf c1 then write(1);
           if this instanceOf c2 then write(2);
           if this instanceOf c3 then write(3);
           return 0;
         }
       }
       class c1 extends c {
         method c1() { return super c(); }
       }
       class c2 extends c {
         method c2() { return super c(); }
       }
       class c3 extends c {
         method c3() { return super c(); }
       }
       class main {
         method main() {
           (new c()).test();
           (new c1()).test();
           (new c2()).test();
           (new c3()).test();
	   return 0;
         }
       }

--- -1 1 -1 2 -1 3

  macro p20 =
       var x;
       class main {
         var a;
         method main() {
           a = 1;
           write(a);
           if (x == 0) then
           {
              x = 1;
              this.main();
           }
           return 0;  
         }
       }

--- 1  1

  macro p21 =
     var x;
     class a {
       var x;
       method a() { x = 1; return 0; }
       method val() { return x; }
     }
     var y ;
     class b {
       var y ;
       method b() { y = 2; return 0; }
       method val() { return y; }
     }
     class main {
       var a; var b;
       method main() {
         a = new a(); write (a.val());
         b = new b(); write (b.val());
         x = 3 ; write(x);
         y = 4; write (y);   
         write(a.val());
         write(b.val());
       }
     }

--- 1 2 3 4 1 2 

  syntax Stmts ::= ss01
  macro ss01 =
     var x;
     x = 2 ;
     x = x + 2;
     write(x);
       

endkm

