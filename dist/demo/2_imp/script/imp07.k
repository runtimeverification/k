module IMP-SYNTAX

  syntax AExp ::= Int | Id | String
                | "++" Id
                | "read" "(" ")"
                > AExp "/" AExp    [left, strict]
                > AExp "+" AExp    [left, strict]
                | "(" AExp ")"     [bracket]
  syntax BExp ::= Bool
                | AExp "<=" AExp   [seqstrict, latex("{#1}\leq{#2}")]
                | "not" BExp       [strict]
                > BExp "and" BExp  [left, strict(1)]
                | "(" BExp ")"     [bracket]
  syntax Stmt ::= "skip"
                | Id ":=" AExp     [strict(2)]
                | "if" BExp
                  "then" Stmt
                  "else" Stmt      [strict(1)]
                | "while" BExp
                  "do" Stmt
  				| "var" Ids              
                | "print" "(" AExps ")"  [strict]
                | "halt"
                > "spawn" Stmt
                > Stmt ";" Stmt    [left]
                | "{" "}"
                | "{" Stmt "}"
                | "(" Stmt ")"     [bracket]

  syntax Ids ::= List{Id,","}      [strict]
  syntax AExps ::= List{AExp,","}  [strict]

endmodule


module IMP
  imports IMP-SYNTAX
  syntax KResult ::= Int | Bool
  
  configuration <T color="yellow">
                  <k color="green"> $PGM:K </k>
                  <env color="LightSkyBlue"> .Map </env>
                  <store color="red"> .Map </store>
                  <nextLoc color="gray"> 0 </nextLoc>
                </T>

  rule <k> X:Id => I ...</k>
       <env>... X |-> N ...</env>
	   <store>... N |-> I ...</env>
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule not(T:Bool) => notBool T
  rule true and B:BExp => B
  rule false and _ => false

  rule skip => .
  rule <k> X := I:Int => . ...</k>
       <env>... X |-> N ...</env>
	   <store>... N |-> (_ => I) ...</store>
  rule S1 ; S2 => S1 ~> S2  [structural]
  rule if true then S else _ => S
  rule if false then _ else S => S
  rule while B do S
    => if B then (S ; while B do S) else skip  [structural]

  rule <k> var (X:Id,Xs:Ids => Xs) ...</k>
       <env> Rho => Rho[N/X] </env>
	   <store>... . => N |-> 0 ...</store>
	   <nextLoc> N => N +Int 1 </nextLoc>
  rule var .Ids => .  [structural]

endmodule
