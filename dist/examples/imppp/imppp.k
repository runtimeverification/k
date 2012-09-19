//require "k-prelude.k"
//require "modules/uris.k"

module IMPPP-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS

  syntax AExp ::= Id | Int
                | AExp "/" AExp   		 [left, superheat, strict]
                > AExp "+" AExp   		 [left, superheat, strict]
                | "(" AExp ")"			 [bracket]
                
  syntax BExp ::= Bool
                | AExp "<=" AExp  		 [seqstrict, latex({#1}\leq{#2})]
                > "not" BExp      		 [strict]
                > BExp "and" BExp 		 [strict(1)]
                | "(" BExp ")"			 [bracket]

  syntax Stmt ::= "skip"
  				| "var" Ids              
                | "print" "(" AExps ")"  [strict]  
                | "halt"
                | Id ":=" AExp    		 [strict(2)]
                | "if" BExp
                  "then" Stmt
                  "else" Stmt     		 [strict(1)]
                | "while" BExp
                  "do" Stmt       		 
                > "spawn" Stmt           
                > Stmt ";" Stmt   		 [left]
                | "(" Stmt ")"    		 [bracket]
                | "{" "}"
                | "{" Stmt "}"
                  
  syntax Ids ::= List{Id,","} [strict]

  syntax AExp ::= String
                | "++" Id         		 
                | "read" "(" ")"

  syntax AExps ::= List{AExp,","} [strict]

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

  rule while B do S:K => if B then S ; while B do S else {}
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
    when fresh(N:Int)
  rule var .Ids => .  [structural]

  syntax K ::= "env" "(" Map ")"
  rule (env(_) => .) ~> env(_)  [structural]
  rule <k> env(Rho) => . ...</k> <env> _ => Rho </env>  [structural]
  
  
endmodule
