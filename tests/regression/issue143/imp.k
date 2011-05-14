--- This is the prefered style to define languages in K-Maude.
--- The language syntax is defined as a BNF grammar,
--- which is used to parse both programs and the semantics.
--- The problem with this style is that K-Maude's parser, which reduces
--- to Maude's parser, is not powerful enough to parse real languages.
--- If one prefers to define an external parser and pass the ASTs
--- to K-Maude, then one may want to choose a fully-labeled or a
--- labeled-syntax style, to completely avoid any syntactic complications.



kmod IMP-SYNTAX is including PL-INT + PL-ID   --- built-in integers and variable identifiers
  syntax AExp ::= Id | Int
                | AExp + AExp [prec 33 gather (E e) format(d b o d) strict]
                | AExp / AExp [prec 31 gather (E e) format(d b o d) strict]
  syntax BExp ::= Bool
                | AExp <= AExp [prec 37 format(d b o d) seqstrict latex "{#1}\leq{#2}"]
                | not BExp [prec 53 format(b o d) strict]
                | BExp and BExp [prec 55 format(d b o d) strict(1)]
  syntax Stmt ::= skip ; [format (b d o)]
                | Id = AExp ; [prec 40 format(d b o b o) strict(2)]
                | Stmt Stmt [prec 60 gather (e E) format (d noi d)]
                | if BExp then Stmt else Stmt [prec 59 format (b o bni n++i bn--i n++i --) strict(1)]
                | while BExp do Stmt [prec 59 format (b o b n++i --)]
  syntax Pgm ::=  var IdList ; Stmt [prec 70 format (nb o d ni d)]
  syntax IdList ::= Id | .IdList | IdList , IdList [assoc id: .IdList]
endkm

kmod IMP-PROGRAMS is including IMP-SYNTAX 
  syntax Id   ::= a | b | c | d | e | f | g | h | i | j | k | l | m
                | n | o | p | q | r | s | t | u | v | w | x | y | z
  syntax Pgm  ::= sumPgm | collatzPgm | countPrimesPgm
  syntax Stmt ::= collatzStmt | multiplicationStmt | primalityStmt

macro sumPgm = (
     var n,s;
     n=10;
     s=0;
     while not(n<=0) do (
       s=s+n;
       n=n+-1;
     )
) 

macro collatzStmt = (
     while not (n<=1) do (
       s=s+1;
       q=n/2;
       r=q+q+1;
       if r<=n
         then n=n+n+n+1; else n=q;
     )
) 

macro collatzPgm = (
   var m,n,q,r,s ;
   m=5;
   s=0;
   while not(m<=2) do (
     n=m;
     m=m+-1;
     collatzStmt
   )
) 

--- fast multiplication (base 2) algorithm
macro multiplicationStmt = ( 
  z=0;
  while not(x<=0) do (
    q=x/2;
    r=q+q+1;
    if r<=x then z=z+y;
    else skip;
    x=q;
    y=y+y;
  )
) 

macro primalityStmt = (
  i=2;
  q=n/i;
  t=1;
  while (i<=q and 1<=t) do (
    x=i;
    y=q;
    multiplicationStmt 
    if n<=z then t=0; else (
      i=i+1;
      q=n/i;
    )
  )
) 

macro countPrimesPgm = (
   var i,m,n,q,r,s,t,x,y,z;
   m=10;
   s=0; n=2;
   while n<=m do (
     primalityStmt
     if 1<=t then s=s+1; else skip;
     n=n+1;
   )
)
endkm

kmod IMP-SEMANTICS is including IMP-SYNTAX + K
  syntax K ::= AExp | BExp | Stmt | Pgm | IdList
  syntax KResult ::= Int | Bool

  configuration <T> <k>.K</k> <br/> <state>.Map</state> </T>

  rule <k>X:Id => I:Int<_/k> <state_>X|->I<_/state> 
  rule '_+_(I1:Int,,I2:Int) => I1 +Int I2
  rule I1 / I2 => I1 /Int I2  if I2 =/=Bool 0 
  rule I1 <= I2 => I1 <=Int I2
  rule not(T:Bool) => notBool T  
  rule true and B:BExp => B  
  rule false and _  => false  
  rule skip; => .
  rule <k>X=I; => .<_/k> <state_> X|->(_=>I) <_/state> 
  rule S1:Stmt S2:Stmt => S1~>S2
  rule if true then S:Stmt else _ => S
  rule if false then _ else S => S
  rule <k>while B do S => if B then (S while B do S) else skip; <_/k>
  rule <k>var Xl:IdList; S => S</k> <br/> <state_>. => getList{K}(Xl)|->0 <_/state> [structural] 
endkm

kmod IMP is including IMP-PROGRAMS + IMP-SEMANTICS 
  syntax Bag ::= [[ KLabel ]] [latex "\llbracket\,{#1}\,\rrbracket"] | pgm
  macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>
  macro pgm = [['sumPgm]]
endkm

