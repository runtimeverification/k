--- in skool-typed-syntax

kmod SKOOL-TYPED-PROGRAMS is including SKOOL-TYPED-SYNTAX

  syntax #Id ::= 
                a | b | c 
              | d | e | f 
              | g | h | i 
              | j | k | l 
              | m | n | o 
              | p | q | r 
              | s | t | u 
              | v | w | x 
              | y | z 
              | aa | bb | cc | dd
              | m0 | m1 | m2 | m3 | m4 | m5
              | aux1 | aux2
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

  syntax ClassDecl ::= 
                p01 | p02 | p03 
              | p04 | p05 | p06 
              | p07 | p08 | p09 
              | p10 | p11 | p12 
              | p13 | p14 | p15 
              | p16 | p17 | p18 
              | p19 | p20 | p21
              | p22 | p23
  
  macro p01 =
       class main {       --- "new main();" statement automatically generated for any program
         var x:int;
         method main() {  --- constructor methods have the same name as the class
                          --- they are called when objects are created for the class
                          --- they need not be typed; their returned value is discarded anyway
           x=1;
           write(x+1);
         }
       }
--- 2


  macro p02 =
       class c {
         var x:int;
         method c() {  --- constructor method, so no need to type it
           x=5;
         }
         method g():int {
           return x;
         }
       }

       class main {
         method main() {
           write((new c()).g());
         }
       }
--- 5


  macro p03 =
       class c {
         var i:int, j:int;
         method c(x:int) {
           i = ++x;
           j = ++x;
         }
         method add (x:int):int {
           i = ++i+x;
           j = ++j-x;
         }
         method write2():int {
           write(i,j);
         }
       }

       class main {
         var x:int, y:int, o:c;
         method main():int {
           x = 0; y = 0; o = new c(5);
           o.write2();
           o.add(3);
           o.write2();
         }
       }
--- 6 7 10 5


  macro p04 =
       class a {  --- classes are not enforced to have constructors
                  --- provided that one never creates instances for them
                  --- indeed, below we only create an instance for a subclass of a (for main)
          method m1(x:int):int {
             return ++x;
          }
       }

       class b extends a {
          var x:int;
          method b() {
             x=3;
          }
       }

       class main extends b {
          method m1(y:int):int {
              return  y*y;
          }
          method main() {
             write(m1(4));
          }
       }
--- 16 (method m1 of main is called)


  macro p05 =
       class a {
          method m1(x:int):int {
             return x+5;
          }
       }

       class b extends a {
          var x:int;
          method b() {
             x=3;
          }
       }

       class main extends b {
          method m1(y:int):int {
              return  y+x ;
          }
          method main() {
             write(m1(4));
          }
       }
--- 4 (because the constructor b() is not called by "new main()")


  macro p06 =
       class a {
          var x:int;
          method a() {
            x=2;
          }
          method m1(x:int):bool {
             return (this.x) == x;  --- this types, because this.x looked up statically
                                    --- this.x therefore refers to the x:int field in a
          }
          method c():int {
             return x;
          }
       }

       class b extends a {
          var x:bool;
          method b() {
             x=false;
             super.a();
          }
       }

       class main {
          method main() {
             var o[5]:a[], p[4]:b[], b:bool ;
             o[0] = new a();
             o[1] = new b();
             p[3] = new b();
             p[2] = new b();
             o[3] = o[1];
             o[4] = p[3];
             b = o[4].m1(3);
             if (not b) then {
               write(p[3].c());
             }
             if (not p[2].m1(2)) then {
               write(p[2].c());
             }
          }
       }
--- 2


macro p07 =
     class point {
       var x:int, y:int;
       method point(initx:int, inity:int) {
         x = initx;
         y = inity;
       }
       method move(dx:int, dy:int):void {
         x = x+dx;
         y = y+dy;
       }
       method writeLocation():void {
         write(x,y);
       }
     }

     class colorpoint extends point {
       var color:int;
       method colorpoint(initx:int, inity:int) {
         x = initx;
         y = inity;
       }
       method setColor(c:int):void {
         color = c;
       }
       method writeColor():int {  --- it is OK to have a return type and no return value
                                  --- a value will be automatically generated (0 here)
         write(color);
       }
     }

     class main {
       method main():int {
         var p:point = new point(3,4), cp:colorpoint = new colorpoint(10,20);
         p.move(3,4);
         p.writeLocation();
         cp.setColor(87);
         cp.move(10, 20);
         cp.writeLocation();
         cp.writeColor();  --- the return value is ignored when used as a statement
         return 0;
       }
     }
--- 6 8 20 40 87


macro p08 =   --- same as the one above, except it has a different colorpoint constructor
              --- and it drops all the useless ":void" types for classes
     class point {
       var x:int, y:int;
       method point(initx:int, inity:int) {
         x = initx;
         y = inity;
       }
       method move(dx:int, dy:int) {
         x = x + dx;
         y = y + dy;
       }
       method writeLocation() {
         write(x,y);
       }
     }

     class colorpoint extends point {
       var color:int;
       method colorpoint(initx:int, inity:int, initcolor:int) {
         x = initx;
         y = inity;
         color = initcolor;
       }
       method setColor(c:int) {
         color = c;
       }
       method writeColor() {
         write(color);
       }
     }

     class main {
       method main() {
         var p:point = new point(3,4), cp:colorpoint = new colorpoint(10,20,87);
         p.move(3,4);
         cp.move(10,20);
         p.writeLocation();
         cp.writeLocation();
         cp.writeColor();
       }
     }
--- 6 8 20 40 87


macro p09 =   --- same as the above, except that the colorpoint constructor
              --- invokes the point construct to initialize the position
     class point {
       var x:int, y:int;
       method point(initx:int, inity:int) {
         x = initx;
         y = inity;
       }
       method move(dx:int, dy:int) {
         x = x + dx;
         y = y + dy;
       }
       method writeLocation() {
         write(x,y);
       }
     }

     class colorpoint extends point {
       var color:int;
       method colorpoint(initx:int, inity:int, initcolor:int) {
         point(initx, inity);
         color = initcolor;
       }
       method setColor(c:int) {
         color = c;
       }
       method writeColor() {
         write(color);
       }
     }

     class main {
       method main() {
         var p:point = new point(3,4), cp:colorpoint = new colorpoint(10,20,87);
         p.move(3,4);
         cp.move(10,20);
         p.writeLocation();
         cp.writeLocation();
         cp.writeColor();
       }
     }
--- 6 8 20 40 87


macro p10 = 
     class c1 {
       var x:int, y:int;
---       method c1() { }  --- not necessary, because we create no instance of c1
       method setx1(v:int) { x=v; }
       method sety1(v:int) { y=v; }
       method getx1():int { return x; }
       method gety1():int { return y; }
     }

     class c2 extends c1 {
       var y:int;
       method c2() { }   --- such empty constructs are necessary when creating instances
                         --- of the class; they are not necessary otherwise (see c1 above)
       method sety2(v:int) { y=v; }
       method getx2():int { return x; }
       method gety2():int { return y; }
     }

     class main {
       method main() {
         var o2:c2 = new c2();
         o2.setx1(11);
         o2.sety1(12); 
         o2.sety2(99);
         write(o2.getx1(), o2.gety1(), o2.getx2(), o2.gety2());
       }
     }
--- 11 12 11  99


macro p11 =
     class c1 {
       method c1() { }
       method m1():int { return 1; }
       method m2():int { return m1(); }
     }

     class c2 extends c1 {
       method c2() { }
       method m1():int { return 2; }
     }

     class main {
       method main() {
         var o1:c1 = new c1(), o2:c2 = new c2();
         write(o1.m1(), o2.m1(), o2.m2());
       }
     }
--- 1 2 2 


macro p12 =
     class c1 {
       method c1() { }
       method m1():int { return 1; }
       method m2():int { return 100; }
       method m3():int { return m2(); }
     }

     class c2 extends c1 {
       method c2() { }
       method m2():int { return 2; }
     }

     class main {
       method main() {
         var o1:c1 = new c1(), o2:c2 = new c2();
         write(o1.m1(), o1.m2(), o1.m3(), o2.m1(), o2.m2(), o2.m3());
       }
     }
--- 1 100 100 1 2 2 


macro p13 =
     class c1 {
       method c1() { }
       method m1():int {
         return(m2());
       }
       method m2():int { return 13; }
     }

     class c2 extends c1 {
       method c2() { }
       method m1():int { return 22; }
       method m2():int { return 23; }
       method m3():int {
         return(super.m1());
       }
     }

     class c3 extends c2 {
       method c3() { }
       method m1():int { return 32; }
       method m2():int { return 33; }
     }

     class main {
       method main() {
         write((new c3()).m3());
       }
     }
--- 33 


macro p14 =  --- tricky program checking dynamic scoping and super
     class a {
       var i:int, j:int;
       method a() {
         j = ++i+1;
       }
       method aa():int {
         j = ++i+1;
         return j;
       }
       method f():int {
         return aa();
       }
       method g():int {
         return f();
       }
       method h():int {
         return i+j;
       }
     }

     class b extends a {
       var j:int, k:int;
       method aa():int {
         return bb();
       }
       method b() {
         super.a();
         j = 10;
         k = j+1;
       }
       method bb():int {
         k = ++j+1;
         return k;
       }
       method g():int {
         return super.h();
       }
       method h():int {
         return g();
       }
     }

     class c extends b {
       method aa():int {
         return super.aa();
       }
       method bb():int {
         return super.bb();
       }
       method c() {
         i = 100;
         j = i+1;
         k = j+1;
       }
       method g():int {
         return i+k*j;
       }
     }

     class main {
       method p(o:a) {
         write(o.f(), o.g(), o.h());
       }
       method main() {
         p(new a());
         p(new b());
         p(new c());
       }
     }
--- 3 4 7 12 3 3 103 10606 10606


macro p15 =   --- tests creating an object inside a method and then returning it
     class i {
       var value:int;
       method i(v:int) {
         value = v;
       }
       method m1():g {
         return (new g(value+9));  --- creates and returns an object
       }
     }

     class g {
       var a:int;
       method g(t:int) {
         a = t;
       }
       method write2() { write(a); }
     }

     class main {
       method main() {
         ((new i(1)).m1()).write2();
       }
     }
--- 10


macro p16 =   --- tests passing objects
     class i {
       var f:int;
       method i(v:int) {
         f = v;
       }
       method get():int { return f; }
     }

     class g {
       var o:i;
       method g(obj:i) {
         o = obj;
       }
       method do():int {
         var f:int = 9;
         return (o.get());
       }
     }

     class main {
       method main() {
         var t:i = new i(1), y:g = new g(t);  --- passes an object
         write(y.do());
       }
     }
--- 1


macro p17 =
class main {
       method f(x:int):int {
         if x <= 1 then return 1; else return(x * (f(x - 1)));
       }
       method main() {
         write(f(f(4)));
       }
}

--- (4!)!, that is, 620448401733239439360000


macro p18 =
     class sorting {
       var input[100]:int[], array[100]:int[], n:int;

       method sorting(x:int) {
         n=x;
       }

       method read2() {
         for i = 0 to n - 1 do {
           input[i] = read();
         }
       }

       method init() {
         for i = 0 to n - 1 do
           array[i] = input[i];
       }

       method write2() {
         for i = 0 to n - 1 do
           write(array[i]);
       }

       method insertionSort() {
         for i = 1 to n - 1 do {
           var j:int, done:bool, t:int = array[i];
           done = false;
           j = i - 1;
           while (j >= 0) and not done do {
             if (array[j] > t) then {
               array[j+1] = array[j];
               j = j - 1;
             } else {
               done = true;
             }
           }
           array[j+1] = t;
         }
       }

       method bubbleSort() {
         var t:int;
         for i = 0 to n - 1 do {
           for j = 0 to n - 2 do {
             if array[j] > array[j+1] then {
               t = array[j+1];
               array[j+1] = array[j];
               array[j] = t;
             }
           }
         }
       }

       method siftDown(root:int, bottom:int) {
         var done:bool=false, maxChild:int, t:int;
         while (root*2 <= bottom and not done) do {
           if (root*2 == bottom) then {
             maxChild = root*2;
           } else if (array[root*2] > array[root*2+1]) then {
                    maxChild = root*2;
                  } else { 
                    maxChild = root*2+1; 
                  }
           if (array[root] < array[maxChild]) then {
             t = array[root];
             array[root] = array[maxChild];
             array[maxChild] = t;
             root = maxChild;
           } else { 
             done = true; 
           }
         }
       }

       method heapSort(){
         var t:int, i:int = (n/2) - 1;
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
       }
     }

     class main {
       method main() {
         var s:sorting = new sorting(read());
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
       }
     }


macro p19 =
     class c {
       method c() {  }
       method test() {
         write(-1);
         if this instanceOf c1 then write(1);
         if this instanceOf c2 then write(2);
         if this instanceOf c3 then write(3);
       }
     }

     class c1 extends c {
       method c1() { super.c(); }
     }

     class c2 extends c {
       method c2() { super.c(); }
     }

     class c3 extends c {
       method c3() { super.c(); }
     }

     class main {
       method main() {
         (new c()).test();
         (new c1()).test();
         (new c2()).test();
         (new c3()).test();
       }
     }
--- -1 -1 1 -1 2 -1 3


macro p20 =  --- this program gets stuck: we do not allow global variables
     var x:int;

     class main {
            var a:int;
            method main() {
              a = 1;
              write(a);
              if (x == 0) then {
                x = 1;
                main();
              }
            }
     }
--- may expect "1  1", but it actually gets stuck


macro p21 =  --- this program gets stuck: we do not allow global variables
     var x:int;

     class a {
       var x:int;
       method a() { x = 1; }
       method val():int { return x; }
     }

     var y:int;

     class b {
       var y:int;
       method b() { y = 2; }
       method val():int { return y; }
     }

     class main {
       var a:a, b:b;
       method main() {
         a = new a(); 
         write (a.val());
         b = new b(); 
         write (b.val());
         x = 3; 
         write(x);
         y = 4; 
         write (y);
         write(a.val());
         write(b.val());
       }
     }
--- 1 2 3 4 1 2 


macro p22 =
     class a {
       var x:int ;
       method a() {
         x=7;
       }
       method m0():int {
         return x;
       }
     }

     class b extends a {
       var x:bool ;
       method b() {
         super.a();
         x=true;
       }
       method m1():int {
         return super.x;
       }
       method m2():int {
         var o:a = this;
         return o.x;            --- implicit casting
                                --- the field x is the one in the type a of o, that is, 7
       }
       method m3():int {
         return (cast this to a).x;  --- explicit casting
                                     ---"cast object to class" casts "object" to "class"
       } 
       method m4():int {
         return aux1(this);
       }
       method aux1(o:a):int {   --- implicit casting, again
         return o.x;
       }
       method m5():bool {
         return aux2(this);
       }
       method aux2(o:a):bool {       --- implicit casting, again
         return (cast o to b).x;     --- but then explicit casting back to b
       }
     }

     class main {
       method main() {
         var o:b = new b();
         write(o.m0(), o.m1(), o.m2(), o.m3(), o.m4(), o.m5());
       }
     }
--- 7 7 7 7 7 true


macro p23 =
     class c1 {
       var v:int = 7;
       method c1() { ++v; }
       method m0():int  { return v; }
       method m1():int  { return -v; }
     }

     class c2 {
       var v:int;
       method c2(x:int) { v=x; }
       method m0():int  { return v; }
       method m1():int  { return -v; }
     }

     class main {
       method main() {
         var o1:c1 = new c1(), o2:c2 = new c2(1);
         write(o1.m0());
         o1.m0 = o1.m1;
         write(o1.m0());
         o1.m0 = o2.m0;
         write(o1.m0());
         o1.m0 = o2.m1;
         write(o1.m0());
         o2.c2(3);
         write(o1.m0());
       }
     }
--- 8 -8 1 -1 -3
endkm
