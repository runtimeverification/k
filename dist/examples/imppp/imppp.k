//require "k-prelude.k"
//require "modules/uris.k"

module IMPPP-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS

  syntax AExp ::= Id | Int
                | AExp "/" AExp   		 [prec(31), left, superheat, strict]
                > AExp "+" AExp   		 [prec(33), left, superheat, strict]
                | "(" AExp ")"			 [bracket]
                
  syntax BExp ::= Bool
                | AExp "<=" AExp  		 [prec(37), seqstrict, latex("{#1}\leq{#2}")]
                > "not" BExp      		 [prec(53), strict]
                > BExp "and" BExp 		 [prec(55), strict(1)]
                | "(" BExp ")"			 [bracket]

  syntax Stmt ::= "skip"
  				| "var" Ids              [prec(70)]
                | "print" "(" AExps ")"  [strict]  
                | "halt"
                > Id ":=" AExp    		 [prec(80), strict(2)]
                > "if" BExp
                  "then" Stmt
                  "else" Stmt     		 [prec(85), strict(1)]
                | "while" BExp
                  "do" Stmt       		 [prec(85)]
                > "spawn" Stmt           [prec(90)]
                > Stmt ";" Stmt   		 [prec(100), left]
                | "(" Stmt ")"    		 [bracket]
                | "{" "}"
                | "{" Stmt "}"           [gather(&)]
                  
  syntax Ids ::= List{Id,","}     		 [strict]

  syntax AExp ::= String
                | "++" Id         		 [prec(0)]
                | "read" "(" ")"

  syntax AExps ::= List{AExp,","}

endmodule

module IMPPP
  imports IMPPP-SYNTAX
  imports BUILTIN-HOOKS
  imports URIS

  configuration
    <T color="yellow">
      <threads color="orange">
        <thread multiplicity="*" color="red">
          <k color="green"> $PGM:K </k>
          <env color="LightSkyBlue"> .Map </env>
        </thread>
     </threads>
//     <br/>
     <store color="white"> .Map </store>
     <nextLoc color="gray"> 0 </nextLoc>
     <in color="magenta" stream="stdin">  .List </in>
     <out color="Orchid" stream="stdout"> .List </out>
    </T>

  syntax KResult ::= Int | Bool

  rule <k> X:Id => I:Int ...</k>
       <env>... X |-> N:Int ...</env>
       <store>... N |-> I ...</store>  [supercool, transition]

  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=Int 0

  rule I1:Int <= I2:Int => I1 <=Int I2
  rule not T:Bool => notBool T
  rule true  and B:BExp => B
  rule false and B:BExp => false

  rule skip => .

  rule <k> X:Id := I:Int => . ...</k>
       <env>... X |-> N:Int ...</env>
       <store>... N |-> (_ => I) ...</store>  [transition]

  rule S1:K ; S2:K => S1 ~> S2  [structural]

  rule if  true then S1:K else _  => S1
  rule if false then _  else S2:K => S2

  rule <k> while B do S:K => if B then S ; while B do S else {} ...</k>
  syntax KResult ::= String
  rule Str1:String + Str2:String => Str1 +String Str2

  rule <k> ++X:Id => I:Int +Int 1 ...</k>
       <env>... X |-> N:Int ...</env>
       <store>... N |-> (I => I +Int 1) ...</store>  [supercool, transition]

  rule <k> read() => I:Int ...</k>
       <in> ListItem(I) => . ...</in>  [transition]

  syntax Printable ::= Int | String
  rule <k> print(P:Printable,AEs:AExps => AEs) ...</k>
       <out>... . => ListItem(P) </out>  [transition]
  rule print(.AExps) => .  [structural]

  rule <threads>... <k> halt ...</k> ...</threads> => <threads> .Bag </threads>

  rule <k> spawn S => . ...</k> <env> Rho </env>
       (. => <thread>... <k> S </k> <env> Rho </env> ...</thread>)

  rule <thread>... <k> .K </k> ...</thread> => .  [structural]

  rule {} => .  [structural]
  rule <k> {S} => S ~> env(Rho) ...</k> <env> Rho:Map </env>  [structural]

  rule <k> var (X,Xl => Xl:Ids) ...</k>
       <env> Rho => Rho[N/X] </env>
       <store>... . => N |-> 0 ...</store>
       <nextLoc> N => N +Int 1 </nextLoc>
  rule var .Ids => .  [structural]

  syntax K ::= "env" "(" Map ")"
  rule (env(_) => .) ~> env(_)  [structural]
  rule <k> env(Rho) => . ...</k> <env> _ => Rho </env>  [structural]
  
  
endmodule
