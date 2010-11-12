--- in skool-typed-syntax

kmod SKOOL-TYPED-PROGRAMS is including SKOOL-TYPED-SYNTAX

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
			  | aa | bb | cc | dd
              | m0 | m1 | m2 | m3 | m4
              | aux
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
              | p22
  
  macro p01 =
       class main {
         var x : int ;
         method main() : int {
           x = 1;
           write(x+1);
           return 0;
         }
       }
--- 2
  macro p02 =
       class c {
         var x : int;
         method c() { x = 5; }
         method g() : int { return x; }
       }
       class main {
         method main() {
           write((new c()).g());
         }
       }
--- 5
  macro p03 =
       class c {
         var i : int;
         var j : int;
         method c ( x : int ) {
           i = x;
           j = ++x;
         }
         method add ( x : int ) : int {
           i = i+x;
           j = j-x;
	   return 0;
         }
         method write2() : int {
           write(i);
           write(j);
	   return 0;
         }
       }

       class main {
         var x : int;
         var y : int;
         var o : c;
         method main() : int {
           x = 0; y = 0; o = new c(5);
           o.write2();
           o.add(3);
           o.write2();
	   return 0;
         }
       }

--- 5 6 8 3

  macro p04 =
       class a {
          method m1(x : int) : int {
             return ++x;
          }
       }
       class b extends a {
          var x : int ;
          method b() {
             x = 3 ;
          }
       }
       class main extends b {
          method m1(y : int) : int {
              return  y * y ;
          }
          method main() {
             write(this.m1(3));
          }
       }

--- 9

  macro p05 =
       class a {
          method m1(x : int) : int {
             return x + 5;
          }
       }
       class b extends a {
          var x : int ;
          method b() {
             x = 3 ;
          }
       }
       class main extends b {
          method m1(y : int) : int {
              return  y + x ;
          }
          method main() {
             write(this.m1(3));
          }
       }

--- 3

  macro p06 =
       class a {
          var x : int;
          method a() {x=2;}
          method m1(x : int) : bool {
---             return (this.x) == x;
             return x == 1;
          }
          method c() : int {
             return x;
          }
       }
       class b extends a {
          var x : bool ;
          method b() {
             x = false ;
             super.a();
          }
       }
       class main {             
          method main() {
             var o[5] : a[];
             var p[4] : b[];
             var b : bool ;
             o[1] = new a();
             o[2] = new b();
             p[3] = new b();
             o[3] = o[1];
             o[4] = p[3];
             b = p[3].m1(3);
             if (not b) then {
               write(p[3].c());
             }
          }
       }

--- 2


macro p07 =
class point {
	var x : int;
	var y : int;
	method point(initx : int, inity : int) : int {
		x = initx;
		y = inity;
		return 0;
	}
	method move(dx : int, dy : int) : int {
		x = x+dx;
		y = y+dy;
		return 0;
	}
	method writeLocation() : int {
		write(x);
		write(y);
		return 0;
	}
}
class colorpoint extends point {
	var color : int;
	method colorpoint(initx : int, inity : int) : int {
		x = initx;
		y = inity;
		return 0;
	}
	method setColor(c : int) : int {
		color = c;
		return 0;
	}
	method writeColor() : int {
		write(color);
		return 0;
	}
}
class main {
	method main() : int {
		var p : point;
		var cp : colorpoint;
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
	var x : int;
	var y : int;
	method point(initx : int, inity : int) {
		x = initx;
		y = inity;
		--- return 0;
	}
	method move(dx : int, dy : int) {
		x = x + dx;
		y = y + dy;
		--- return 0;
	}
	method writeLocation() {
		write(x);
		write(y);
		--- return 0;
	}
}
class colorpoint extends point {
	var color : int;
	method colorpoint(initx : int, inity : int, initcolor : int) {
		x = initx;
		y = inity;
		color = initcolor;
		--- return 0;
	}
	method setColor(c : int) {
		color = c;
		--- return 0;
	}
	method writeColor() {
		write(color);
		--- return 0;
	}
}
class main {
	method main() {
		var p : point;
		var cp : colorpoint;
		p = new point(3,4);
		cp = new colorpoint(10,20,87);
		p.move(3,4);
		cp.move(10,20);
		p.writeLocation();
		cp.writeLocation();
		cp.writeColor();
		--- return 0;
	}
}

macro p09 =
class point {
	var x : int;
	var y : int;
	method point(initx : int, inity : int) {
		x = initx;
		y = inity;
		--- return 0;
	}
	method move(dx : int, dy : int) {
		x = x + dx;
		y = y + dy;
		--- return 0;
	}
	method writeLocation() {
		write(x);
		write(y);
		--- return 0;
	}
}
class colorpoint extends point {
	var color : int;
	method colorpoint(initx : int, inity : int, initcolor : int) {
		this.point(initx, inity);
		color = initcolor;
		--- return 0;
	}
	method setColor(c : int) {
		color = c;
		--- return 0;
	}
	method writeColor() {
		write(color);
		--- return 0;
	}
}
class main {
	method main() {
		var p : point;
		var cp : colorpoint;
		p = new point(3,4);
		cp = new colorpoint(10,20,87);
		p.move(3,4);
		cp.move(10,20);
		p.writeLocation();
		cp.writeLocation();
		cp.writeColor();
		--- return 0;
	}
}

--- 6 8 20 40 87

macro p10 = 
class c1 {
	var x : int;
	var y : int;
	method c1() { }
	method setx1(v : int) { x = v;}
	method sety1(v : int) { y = v;}
	method getx1() : int { return x; }
	method gety1() : int { return y; }
}
class c2 extends c1 {
	var y : int;
	method c2() { }
	method sety2(v : int) { y = v;}
	method getx2() : int { return x; }
	method gety2() : int { return y; }
}
class main {
	method main() {
		var o2 : c2;
		o2 = new c2();
		o2.setx1(11);
		o2.sety1(12); 
		o2.sety2(99);
		write(o2.getx1());
		write(o2.gety1());
		write(o2.getx2());
		write(o2.gety2());
	}
}

--- 11 12 11  99

macro p11 =
class c1 {
	method c1() { }
	method m1() : int { return 1; }
	method m2() : int { return this.m1(); }
}
class c2 extends c1 {
	method c2() { }
	method m1() : int { return 2; }
}
class main {
	method main() {
		var o1 : c1;
		var o2 : c2;
		o1 = new c1();
		o2 = new c2();
		write(o1.m1());
		write(o2.m1());
		write(o2.m2());
	}
}

--- 1 2 2 

macro p12 =
class c1 {
	method c1() { }
	method m1() : int { return 1; }
	method m2() : int { return 100; }
	method m3() : int { return this.m2(); }
}
class c2 extends c1 {
	method c2() { }
	method m2() : int { return 2; }
}
class main {
	method main() {
		var o1 : c1;
		var o2 : c2;
		o1 = new c1();
		o2 = new c2();
		write(o1.m1());
		write(o1.m2());
		write(o1.m3());
		write(o2.m1());
		write(o2.m2());
		write(o2.m3());
	}
}

--- 1 100 100 1 2 2 

macro p13 =
class c1 {
	method c1() { }
	method m1() : int {
		return(this.m2());
	}
	method m2() : int { return 13; }
}
class c2 extends c1 {
	method c2() { }
	method m1() : int { return 22; }
	method m2() : int { return 23; }
	method m3() : int {
		return(super.m1());
	}
}
class c3 extends c2 {
	method c3() { }
	method m1() : int { return 32; }
	method m2() : int { return 33; }
}
class main {
	method main() {
		var o3 : c3;
		o3 = new c3();
		write(o3.m3());
	}
}

--- 33 

macro p14 =
class a {
	var i : int;
	var j : int;
	method a() {
		i = 1;
		j = i + 1;
		--- return j;
	}
	method aa() : int {
		i = 1;
		j = i + 1;
		return j;
	}
	method f() : int {
		return this.aa();
	}
	method g() : int {
		return this.f();
	}
	method h() : int {
		return (i + j);
	}
}
class b extends a {
	var j : int;
	var k : int;
	method aa() : int {
		return this.bb();
	}
	method b() {
		super.a();
		j = 10;
		k = j + 1;
		--- return k;
	}
	method bb() : int {
		--- super.a();
		j = 10;
		k = j + 1;
		return k;
	}
	method g() : int {
		return super.h();
	}
	method h() : int {
		return this.g();	   
	}
}
class c extends b {
	method aa() : int {
		return super.aa();
	}
	method bb() : int {
		return super.bb();
	}
	method c() {
		i = 100;
		j = i + 1;
		k = j + 1;
		--- return k;
	}
	method cc() : int {
		i = 100;
		j = i + 1;
		k = j + 1;
		return k;
	}
	method g() : int {
		return (i + k * j);
	}
}
class main {
	method p(o : a) {
		write(o.f());
		write(o.g());
		write(o.h());
	}
	method main() {
		this.p(new a());
		this.p(new b());
		this.p(new c());
	}
}

--- 2 2 3 11 3 3 11 210 210


macro p15 =
class i {
	var value : int;
	method i(v : int) {
		value = v;
	}
	method m1() : g {
		return (new g(value + 9));
	}
}
class g {
	var a : int;
	method g(t : int) {
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

macro p16 =
class i {
	var f : int;
	method i(v : int) {
		f = v;
	}
	method get() : int { return f; }
}
class g {
	var o : i;
	method g(obj : i) {
		o = obj;
	}
	method do() : int {
		var f : int;
		f = 9;
		return (o.get());
	}
}
class main {
	method main() {
		var t : i;
		var y : g;
		t = new i(1);
		y = new g(t);
		write(y.do());
	}
}

--- 1


macro p17 =
class main {
	method f(x : int) : int {
		if x <= 1 then return 1; else return(x * (this.f(x - 1)));
	}
	method main() {
		write(this.f(this.f(5)));
	}
}

--- (5!)!
--- 6689502913449127057588118054090372586752746333138029810295671352301633557244962989366874165271984981308157637893214090552534408589408121859898481114389650005964960521256960000000000000000000000000000

macro p18 =
class sorting {
	var input[100] : int[];
	var array[100] : int[];
	var n : int;

	method sorting(x : int) {
		n = x;
	}

	method read2() {
		for i = 0 to (n - 1) do {
			input[i] = read();
		}
	}

	method init() {
		for i = 0 to (n - 1) do
			array[i] = input[i];
	}

	method write2() {
		for i = 0 to (n - 1) do
			write(array[i]);
	}

	method insertionSort() {
		for i = 1 to n - 1 do {
			var j : int;
			var done : bool;
			var t : int;
			t = array[i];
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
			array[j + 1] = t;
		}
	}

	method bubbleSort() {
		var t : int;
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

	method siftDown(root : int, bottom : int) {
		var done : bool;
		var maxChild : int;
		var t : int;
		done = false;
		
		while (root*2 <= bottom and not done) do {
			if (root*2 == bottom) then {
				maxChild = root * 2;
			} else if (array[root * 2] > array[root * 2 + 1]) then {
				maxChild = root * 2;
			} else { 
				maxChild = root * 2 + 1; 
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
		var t : int;
		var i : int;
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
	}
}
class main {
	method main() {
		var s : sorting;
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
	}
}


macro p22 = 

   class a {
     var x : int ;
     method a() {
       x=7;
     }
     method m0() : int {
       return x;
     }
   }
   class b extends a {
     var x : bool ;
     method b() {
       super.a();
       x=true;
     }
     method m1() : int {
       return super.x;
     }
     method m2() : int {
       var o:a;
       o=this;
       return o.x;
     }
     method m3() : int {
       return (this as a).x;
     } 
     method m4() : int {
       return aux(this);
     }
     method aux(o:a) : int {
       return o.x;
     }
   }
   class main {
     method main() {
       var o:b;
       o=new b();
       write(o.m0());
       write(o.m1());
       write(o.m2());
       write(o.m3());
       write(o.m4());
     }
   }
--- 7 7 7 7 7
endkm

