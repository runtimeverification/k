kmod STRICT-JAVASCRIPT-PROGRAMS 
	is including STRICT-JAVASCRIPT-SYNTAX 
  
	syntax Id   ::= a | b | c | d | e | f | g | h | i | j | k | l | m
	              | n | o | p | q | r | s | t | u | v | w | x | y | z
	
	syntax Id	::= length | scale
	
	syntax Exp  ::= te0 | te1 | te2 | te3 | te4 | te5 | te6 | te7
				  | ie0 | ie1 | ie2 | ie3 | ie4 | ie5 | ie6 | ie7
				  | e0 | e1 | e2 | e3 | e4 | e5 | e6 | e7 | e8 | e9 | e10 | e11 | e12
				  | ae0 | ae1 | ae2 | ae3 | ae4 | ae5 | ae6 | ae7
				  | ac0 | ac1 | ac2 | ac3 | ac4 | ac5 | ac6 | ac7
				  | l0 | l1 | l2 | l3 | l4 | l5 | l6 | l7 | l8 | l9
	syntax ExecutionStmts ::= es0 | es1 | es2 | es3 | es4 | es5 | es6 | es7 | es8 | es9
	syntax Stmt ::= s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10 | s11
				  | s12 | s13 | s14 | s15 | s16 | s17 | s18 | s19 | s20 | s21 | s22
	
	syntax Case ::= c0 | c1 | c2 | c3 | c4 | c5 | c6

	macro te1 = a
	
	macro te2 = b.scale
	
	macro te3 = 123.scale
	
	macro te4 = b[c]
	
	--- macro te5 = "maurice".length
	
	--- macro te6 = a.b["x"][1]
	
	--- macro te7 = a.b["cut"][1]
	
	macro ie0 = x ( )
	
	macro ie1 = x ( .List{CommaElem} )
	
	macro ie2 = y(a + 3 * c)
	
	macro ie3 = z(a,b) / 4 
	
	macro ie4 = q(1,2,3) && !r || v(false)
	
	macro ie5 = q(r(s(3)))

	macro ie6 = q( r(s(3), t(5)), 2.3 )
	
	macro e0 = t(2)(true)[g](false)
	
	macro e1 = r(1,2).u[q(3)]
	
	macro e2 = new r(true)
	
	macro e3 = delete r
	
	macro e4 = delete r.t
	
	macro e5 = delete r(1)(3.0, 4.2)[w] 
	
	macro e6 = w(3,4)
	
	macro ae0 = 3+5

	macro ae1 = (3<=5) && !(5<=1)
	
	macro ae2 = -3
	
	macro ae3 = +3.4
	
	macro ae4 = 2 - -3  --- 	
	macro ae4 = 2 - -_(3.1)
	
	macro ae5 = r(+3 + -4, -4 - -4)
	
	macro e7 = typeof t
	
	macro e8 = typeof r(s(2))

	macro e9 = typeof r(s(2), t <= u)

	macro e10 = typeof t === r

	macro e11 = r ? e : f

	macro e12 = typeof t === r ? a+b : !c > d + e
---	macro e12 = typeof t === r ? a+b : !c > d || e
	
---	macro ae2 = var x; var y; y = 1 + y;

	macro ac0 = (x = y)
	
	--- macro ac1 = x = 4
	macro ac1 = (x.r[w] = 4)
	
	macro ac2 = (x = y += r(4))
	
	macro ac3 = r[s]() 

	macro ac4 = r[s](1,2) 
	
---	macro es0 = ;;;
	
	macro es1 = r(2); s = new t(true); x = y / z ; return 3 + 4; 
	
	macro es2 = return;
	
	macro es3 = throw s(2);
	
	macro es4 = x = y = 34; break a;
	
	macro s11 = if (q) { if(p) { x = y ;} }
	
	macro s0 = if (x <= 5) { throw s(2); }

	macro s1 = if (x <= 5 || y && z === 3) { q = r; s(2);}
	
	macro s2 = if (y) { r[s](); } else { x = z; }
	
	macro s3 = if (y) {r.s(); } else { x = z; }
	
	macro s4 = if (y) {r.t[s](); } else { x = z; }

	macro s5 = if (y) { r(); } else { x = z; }
	
	macro s6 = if (y) { r(); } else if ( r > s ) { x = z; }
	
	macro s7 = if (y) { r(); } else if ( r > s ) { x = z; } else { return {x: 3, y: 4, z: 5}; }
	
	macro s8 = try { s(0); t(0); } catch ( x ) { return x.u(t()); }
	
	macro s9 = if (y) { r(); } else if ( r > s ) { x = z; } else { if (q) { return 3; } }
	
	macro s10 = try { if (z) {s(0); t(0);} } catch ( x ) { return x.u(t()); }

	macro s11 = return {x: 3, y: 4, z: 5}; 
	
	macro s12 = ;
	
	macro s13 = switch (x < y) {case 0 : r() ; case 1 : s(0)}
	
	macro c0 = case 0 : r() ; break n

	macro c1 = case 0 : r() ; s() ; return
	
---	macro c2 = case 1 : case 2 : case 3 : s() 
	 
	--- macro c3 = case 1 : case 2 : case 3 : s(0); x = y; return {e:2} 
	
	macro c4 = case 1 : case 2 : case 3 : s() ; t() 
endkm
