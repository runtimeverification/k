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

