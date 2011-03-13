require silok-syntax

kmod SILOK-PROGRAMS is including SILOK-SYNTAX 

syntax Pgm ::= pgm1 | pgm2 | pgm3 | pgm4 | pgm5 | pgm6 | pgm7
syntax Id ::=	g1 | g2 | g3 
       	      | l1 | l2 | l3
syntax ProcId ::=  p0 | p1 | p2

macro pgm1 =
  gvars: g1, g2, g3
  lvars: l1, l2, l3 
  {
  main :: g1 := new ; g2 := g1 ; [ g2 = g1 ] g3 := new ;
  g3 := new ; g3 := new ; g3 := new ; g2 := new 
  }

macro pgm2 =
  gvars: g1, g2, g3
  lvars: l1, l2, l3 
  {
  main :: g1 := new ; g2 := g1 ; [ g2 = g1 ] g3 := new ;
	 [ g1 = g2 ] l3 := g3 ; 
	 p1 ; breakpoint ; ( [ l3 /= g3 ] g2 := l2 + g3 := new ) ;
	 [ l3 = g3 ] g2 := new ; p1 ; l2 := g2 ; p2

  p1 :: l3 := g1 ; g1 := new ; l2 := l3 

  p2 :: g2 := l2 ; [ g1 = g2 ] l3 := g3
  }

macro pgm3 =
  gvars: g1, g2
  lvars: l1, l2
  {
  main :: p0
  p0 :: l1 := new ; 
       [ g1 = l2 ] ( g1 := l1 ; p0 ) + [ g1 /= g2 ] ( g2 := g1 ; g1 := l2 ; p0 )
  }

macro pgm4 =
  gvars: g1, g2
  lvars: l1, l2
  {
  main :: p0
  p0 :: l1 := new ; [ g1 = l2 ] ( g1 := l1 ; p0 )
  }

macro pgm5 =
  gvars: g1, g2
  lvars: l1, l2
  {
  main :: g2 := new ; l2 := g2 ; p0 
  p0 :: g2 := new
  }

macro pgm6 =
  gvars: g1, g2
  lvars: l1, l2
  {
  main :: g2 := new ; l2 := g2 ; l1:= new ; g1 := l1 ; p0 ; breakpoint
  p0 :: g2 := new
  }

macro pgm7 =
  gvars: g1, g2
  lvars: l1, l2
  {
  main :: g2 := new ; l2 := g2 ; l1:= new ; g1 := l1 ; p0 ; breakpoint
  p0 :: g2 := new ; l1 := g1 ; p1 --- ; breakpoint
  p1 :: g2 := new ; l1 := g2
  }

endkm

