module RESULT
    imports SUBSTITUTION

    syntax Exp ::= Id
                 | Int
                 | Bool
                 | Exp "i+" Exp [strict, klabel('_i+_)]
                 | Exp "i-" Exp [strict, klabel('_i-_)]
                 | Exp "i==" Exp [strict, klabel('_i==_)]
                 | Exp "i<" Exp [strict, klabel('_i<_)]
                 | "(" Exp ")" [bracket, klabel('(_))]
                 | "LExp" Id ":" Exp

    syntax Stmt ::= Id ":=" Exp [strict(2), klabel('_:=_)]
                  | "skip" [klabel('skip)]
                  | Stmt ";" Stmt [left, klabel('_;_)]
                  | "if" Exp "then" Stmt "else" Stmt [strict(1), klabel
                  ('if_then_else_)]
                  | "while" Exp "do" Stmt [klabel('while_do_)]
                  | "{" Stmt "}" [bracket, klabel('{_})]
                  | "LStmt" Id ":" Stmt

    syntax Code ::= Exp
                  | Stmt
                  | "LCode" Id ":" Code

    syntax KResult ::= Int
                     | Bool
                     | "LKResult" Id ":" KResult

    rule <k1> skip => .K ...</k1>

    rule <k1> I:Id => I1:Int ...</k1> <env1>... I |-> I1 ...</env1>

    rule <k1> I1:Int i+ I2:Int => I1 +Int I2 ...</k1>

    rule <k1> I1:Int i- I2:Int => I1 -Int I2 ...</k1>

    rule <k1> I1:Int i== I2:Int => I1 ==Int I2 ...</k1>

    rule <k1> I1:Int i< I2:Int => I1 <Int I2 ...</k1>

    rule <k1> I:Id := I1:Int => .K ...</k1> <env1>... I |-> ((_:K => I1)) ...
      </env1>

    rule <k1> I:Id := I1:Int => .K ...</k1> <env1> Rho:Map ((.Map => I |-> I1
      )) </env1> when notBool (I in (keys (Rho)))

    rule <k1> S1:Stmt ; S2:Stmt => S1 ~> S2 ...</k1>

    rule <k1> if true then S1:Stmt else _:K => S1 ...</k1>

    rule <k1> if false then _:K else S2:Stmt => S2 ...</k1>

    rule <k1> while E:Exp do S:Stmt => if E then (S ; (while E do S)) else 
      skip ...</k1>

    syntax FExp ::= Id
                  | FExp "f+" FExp [strict, klabel('_f+_)]
                  | FExp "f-" FExp [strict, klabel('_f-_)]
                  | FExp "f==" FExp [strict, klabel('_f==_)]
                  | FExp "f<" FExp [strict, klabel('_f<_)]
                  | "if" FExp "then" FExp "else" FExp [strict(1), klabel
                  ('if_then_else_)]
                  | Val
                  | "fix" Id FExp [binder, klabel('fix__)]
                  > FExp FExp [seqstrict, klabel('__)]
                  | "(" FExp ")" [bracket, klabel('(_))]
                  | "LFExp" Id ":" FExp

    syntax Val ::= "lambda" Id "." FExp [binder, klabel('lambda_._)]
                 | Int
                 | Bool
                 | "LVal" Id ":" Val

    syntax KResult ::= Val
                     | "LKResult" Id ":" KResult

    rule <k2> I1:Int f+ I2:Int => I1 +Int I2 ...</k2>

    rule <k2> I1:Int f- I2:Int => I1 -Int I2 ...</k2>

    rule <k2> I1:Int f== I2:Int => I1 ==Int I2 ...</k2>

    rule <k2> I1:Int f< I2:Int => I1 <Int I2 ...</k2>

    rule <k2> if true then S1:FExp else _:K => S1 ...</k2>

    rule <k2> if false then _:K else S2:FExp => S2 ...</k2>

    rule <k2> (lambda X:Id . E:FExp) V:Val => E [ V / X ] ...</k2>

    rule <k2> fix X:Id E:FExp => E [ (fix X E) / X ] ...</k2>

    configuration
        <aggregation>
                <first>
                    <t1>
                        <k1>
                            $PGM:K
                        </k1>
                        <env1>
                            .Map
                        </env1>
                    </t1>
                </first>
            <second>
                <t2>
                    <k2>
                        $PGM:K
                    </k2>
                </t2>
            </second>
        </aggregation>

endmodule
