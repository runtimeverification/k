
module IMP-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS 
  
  syntax AExp ::= Int | Id
  				| AExp "/" AExp [left, strict]
  				| AExp "*" AExp [left, strict]
  				> AExp "+" AExp [left, strict]
  				| "(" AExp ")"  [bracket]

  syntax BExp ::= Bool
  				| AExp "<=" AExp  [seqstrict]
  				| "not" BExp      [strict]
  				> BExp "and" BExp [left, strict(1)]
  				| "(" BExp ")"    [bracket]

  syntax Stmt ::= "skip"
  				| Id ":=" AExp   [strict(2)]
  				| "if" BExp "then" Stmt "else" Stmt [strict(1)]
  				| "while" BExp "do" Stmt
  				> Stmt ";" Stmt   [left]
  				| "(" Stmt ")"    [bracket]

  syntax Pgm ::= "var" Ids ";" Stmt
  syntax Ids ::= List{Id, ","}
  syntax Start ::= Pgm  

endmodule

module SYMBOLIC-CALCULUS

  syntax #Id ::= "i" | "n" | "s" | "k" 

  syntax IntSymVar ::= "n0" | "s0" | "i0"

  syntax Int ::= IntSymVar

  rule 'isInt(I1:Int -Int I2:Int) => true [anywhere]
  rule 'isInt(I1:Int +Int I2:Int) => true [anywhere]
  rule 'isInt(I1:Int *Int I2:Int) => true [anywhere] 
  rule 'isInt(I1:Int /Int I2:Int) => true [anywhere]


  syntax Bool ::= "isIntSymExp" "(" K ")" | "isBoolSymExp" "(" K ")"


  rule isBoolSymExp(I1:Int <=Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]
  rule isBoolSymExp(I1:Int <=Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

  rule isBoolSymExp(I1:Int ==Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isBoolSymExp(I1:Int ==Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

  rule isBoolSymExp(B1:Bool andBool I2:Bool) => true
       when isBoolSymExp(B1) ==K true
       [anywhere]

  rule isBoolSymExp(B1:Bool orBool I2:Bool) => true
       when isBoolSymExp(B1) ==K true
       [anywhere]
/*
  rule 'isBool(K:K) => true
       when isBoolSymExp(K) ==K true
       [anywhere]
*/

 
  rule isIntSymExp(I1:Int +Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int +Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

 
  rule isIntSymExp(I1:Int -Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int -Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int *Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int *Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int /Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int /Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

  rule 'isInt(K:K) => true
       when isIntSymExp(K) ==K true
       [anywhere]

  rule isIntSymExp(K:K) => true
       when 'isIntSymVar(K) ==K true
       [anywhere]

  rule (I:Int ==Int I:Int) => true [anywhere]

  rule (I:Int *Int I +Int I +Int I +Int 1)
       => 
       (I +Int 1) *Int (I +Int 1)
       [anywhere]
endmodule


module IMP
  imports IMP-SYNTAX
  imports SYMBOLIC-CALCULUS

  configuration <T color="yellow"> 
                  <tasks> 
                    <task multiplicity="*">
                      <config multiplicity="*">
                        <k color="green"> .K  </k>
                        <env color="red"> .Map </env>
                      </config>
                      <formula> true </formula>
                    </task>
                  </tasks>
                </T>


  syntax KResult ::= Int | Bool

// **********************


  rule [addition] : I1:Int + I2:Int => I1 +Int I2 
  rule [multiplication] : I1:Int * I2:Int => I1 *Int I2 
  rule [division] : I1:Int / I2:Int => I1 /Int I2 when I2 =/=K 0


  rule [leq] : I1:Int <= I2:Int => I1 <=Int I2
  rule [not] : not T:Bool => notBool T
  rule [and-true] : true and B:BExp => B
  rule [and-false]: false and B:BExp => false


  rule <task>
         <config>
           <k> B:K ~> K1:K </k>
           <env> Rho1:Map  </env>
         </config>
         <config>
           <k> K2:K </k>
           <env> Rho2:Map </env>
         </config>
         C:Bag
       </task>
       =>
       <task>
         <config>
           <k> true ~> K1 </k>
           <env> Rho1:Map (B |-> true) </env>
         </config>
         <config>
           <k> K2 </k>
           <env> Rho2:Map (B |-> true) </env>
         </config>
         C
       </task>
       <task>
         <config>
           <k> false ~> K1 </k>
           <env> Rho1:Map (B |-> false) </env>
         </config>
         <config>
           <k> K2 </k>
           <env> Rho2:Map (B |-> false) </env>
         </config>
         C
       </task>
       when isBoolSymExp(B)
            andBool notBool(B in keys(Rho1))
            andBool notBool(B in keys(Rho2))

  rule <k> B:K => V ...</k>
       <env>... B |-> V:Bool ...</env>
       when isBoolSymExp(B)

  rule [sequential] : S1;S2 => S1 ~> S2 [structural]

  rule [if-true] : if true  then S:Stmt else _ => S
//       [transition]

  rule [if-false]: if false then _ else S:Stmt => S
 //      [transition]
/*
  rule <task>
        <config>
          <k> if B:Bool then S1:Stmt else S2:Stmt ~> K:K </k>
          C1:Bag
        </config>
        C2:Bag
        <formula> F:Bool </formula>
      </task>
      => 
      (<task>
        <config>
          <k> S1 ~> K </k>
          C1:Bag
        </config>
        C2:Bag
        <formula> F andBool B </formula>
       </task>
       <task>
        <config>
          <k> S2 ~> K </k>
          C1:Bag
        </config>
        C2:Bag
        <formula> F andBool (notBool B) </formula>
       </task>)
      when isBoolSymExp(B)
      [transition]
*/
  rule [skip] : skip => .


  rule [while] : <k> while B:BExp do S:Stmt
                     => 
                     if B then S ; while B do S else skip
                 ...</k>
                 <formula> _ => false </formula>
                 [transition]

  rule [program-no-vars]: <k> var .Ids ; S:Stmt => S ...</k> [structural]


  rule [lookup] :      <k> X:Id => I:Int ...</k>
                      <env>... X |-> I ...</env> 

  rule [assignment]: <k> X:Id := I:Int => . ...</k>
                      <env>... X |-> (_ => I) ...</env>
       [transition]

  rule [program-still-vars]:
           <k> var X:Id, Xs:Ids; S:Stmt => var Xs; S ...</k>
          <env> Rho:Map (. => X |-> 0) </env> when notBool(X in keys(Rho))

// ******* hypotheses *****

  syntax Bag ::= "success"

  rule success success => success 

/*
  rule [equality] :
       <task>
         <config>
           <k> K:K </k>
           <env> n |-> N:Int s |-> S:Int i |-> I:Int Env:Map </env>
         </config>
         <config>
           <k> K </k>
           <env> n |-> N s |-> S i |-> I Env':Map </env>
         </config>
         <formula> F:K </formula>
       </task>
       =>
       success
//       [transition]
*/
  rule [unsat] :
       <task>
         <config>
           <k> .K </k>
           <env> _:Map </env>
         </config>
         <config>
           <k> K:K </k>
           <env> _:Map </env>
         </config>
         <formula> _:Bool </formula>
       </task>
       =>
       .
//       [transition]


// *******

  rule <T> 
         <tasks>
           .
         </tasks>
       </T>
        =>
        <T> 
         <tasks>
            <task>
               <config>
                  <k> 
/*
var i, (s, (n, .Ids));
n := 5;
s := 0;
i := 1;
*/
while (i <= n) do (
  s := s + i * i;
  i := i + 1
)
                    </k>
                  <env> n |-> n0 s |-> s0 i |-> i0  </env>
//                   <env> .Map </env>
                </config>
                <config>
                  <k>
/*
var i, (s, (k, (n, .Ids)));
n := 5;
s := 0;
i := 1;
k := 1;
*/
while (i <= n) do (
  s := s + k;
  (k := k + i + i + 1;
   i := i + 1)
)
/*
while (i <= n) do (
  s := s + i * i;
  i := i + 1
)
*/
                   </k>
                   <env> n |-> n0 s |-> s0 i |-> i0 k |-> i0 *Int i0  </env>
//                   <env> .Map </env>
                 </config>
                 <formula> true </formula>
               </task>
         </tasks>
       </T>

rule [circularity] :
            ( <task>
               <config>
                  <k> 
/*
var i, (s, (n, .Ids));
n := 5;
s := 0;
i := 1;
*/
while (i <= n) do (
  s := s + i * i;
  i := i + 1
)
                    </k>
                  <env>
                       i |-> I1:Int
                       s |-> S1:Int 
                  ...</env>
                </config>
                <config>
                  <k>
/*
var i, (s, (k, (n, .Ids)));
n := 5;
s := 0;
i := 1;
k := 1;
*/
while (i <= n) do (
  s := s + k;
  (k := k + i + i + 1;
   i := i + 1)
)
/*
while (i <= n) do (
  s := s + i * i;
  i := i + 1
)
*/
                   </k>
                   <env> i |-> I2:Int
                         s |-> S2:Int 
                         k |-> K2:Int
                   ...</env>
                 </config>
                 <formula> false </formula>
               </task>)
       => success
  when (I1 ==Int I2)
       andBool (S1 ==Int S2)
       andBool (K2 ==Int I2 *Int I2)

endmodule
