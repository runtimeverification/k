
kmod IMP-SYNTAX is including PL-INT + PL-ID   --- built-in integers and variable identifiers
  syntax AExp ::= Id | Int
                | AExp + AExp                  [prec 33 gather (E e) strict]
                | AExp / AExp                  [prec 31 gather (E e) strict]
  syntax BExp ::= Bool
                | AExp <= AExp                 [prec 37 strict]
                | not BExp                     [prec 53 strict]
                | BExp and BExp                [prec 55 strict(1)]
  syntax Stmt ::= skip ;
                | Id = AExp ;                  [prec 40 strict(2)]
                | Stmt Stmt                    [prec 60 gather (e E)]
                | if BExp then Stmt else Stmt  [prec 59 strict(1)]
                | while BExp do Stmt           [prec 59]
endkm


kmod IMP-PROGRAMS is including IMP-SYNTAX
  syntax Id   ::= a | b | c | d | e | f | g | h | i | j | k | l | m
                | n | o | p | q | r | s | t | u | v | w | x | y | z
  syntax Stmt ::= sumPgm
                | collatzPgm | collatzStmt
                | multiplicationStmt | primalityStmt | countPrimesPgm

macro sumPgm = (
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
  syntax K ::= AExp | BExp | Stmt
  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <k color="green"> .K </k>
                  <state color="red"> .Map </state>
                </T>

  rule <k> X:Id => Sigma(X) <_/k> <state> Sigma:Map </state>
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1 / I2 => I1 /Int I2  if I2 =/=Bool 0 
  rule I1 <= I2 => I1 <=Int I2
  rule not(T:Bool) => notBool T  
  rule true and B:BExp => B  
  rule false and _ => false  
  rule skip; => .
  rule <k> X=I:Int; => . <_/k> <state> Sigma => Sigma[I/X] </state> 
  rule S1:Stmt S2:Stmt => S1~>S2
  rule if true then S:Stmt else _ => S
  rule if false then _ else S => S
  rule <k> while B do S => if B then (S while B do S) else skip; <_/k>
endkm

kmod IMP is including IMP-PROGRAMS + IMP-SEMANTICS 
  syntax Bag ::= [[ KLabel ]] [latex "\llbracket\,{#1}\,\rrbracket"]
  macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>
endkm
