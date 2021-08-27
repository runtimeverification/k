module LESSON-17-B
  imports INT
  imports BOOL
  imports ID-SYNTAX

  syntax Stmt ::= Id "=" Exp ";" [strict(2)]
                | "return" Exp ";" [strict]
  syntax Stmts ::= List{Stmt,""}
  syntax Exp ::= Id 
               | Int 
               | Exp "+" Exp [seqstrict]
               | "spawn" "{" Stmts "}"
               | "join" Exp ";"

  configuration <threads>
                  <thread multiplicity="*" type="Map">
                    <id> 0 </id>
                    <k> $PGM:Stmts </k>
                  </thread>
                </threads>
                <state> .Map </state>
                <next-id> 1 </next-id>

  rule <k> X:Id => I:Int ...</k>
       <state>... X |-> I ...</state>
  rule <k> X:Id = I:Int ; => . ...</k>
       <state> STATE => STATE [ X <- I ] </state>
  rule <k> S:Stmt Ss:Stmts => S ~> Ss ...</k>
  rule <k> I1:Int + I2:Int => I1 +Int I2 ...</k>

  rule <thread>...
         <k> spawn { Ss } => NEXTID </k>
       ...</thread>
       <next-id> NEXTID => NEXTID +Int 1 </next-id>
       (.Bag => 
       <thread>
         <id> NEXTID </id>
         <k> Ss </k>
       </thread>)

  rule <thread>...
         <k> join ID:Int ; => I ...</k>
       ...</thread>
       (<thread>
         <id> ID </id>
         <k> return I:Int ; ...</k>
       </thread> => .Bag)

  syntax Bool ::= isKResult(K) [function, symbol]
  rule isKResult(_:Int) => true
  rule isKResult(_) => false [owise]
endmodule
