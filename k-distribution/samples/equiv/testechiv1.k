// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module TESTECHIV1
    imports SUBSTITUTION

    syntax Exp ::= Id
                 | Int
                 | Bool
                 | Exp "i+" Exp [strict, klabel('_i+_)]
                 | Exp "i-" Exp [strict, klabel('_i-_)]
                 | Exp "i==" Exp [strict, klabel('_i==_)]
                 | Exp "i<" Exp [strict, klabel('_i<_)]
                 | "(" Exp ")" [bracket, klabel('(_))]
                 > "L1Exp" Id ":" Exp

    syntax Stmt ::= Id ":=" Exp [strict(2), klabel('_:=_)]
                  | "skip" [klabel('skip)]
                  | Stmt ";" Stmt [left, klabel('_;_)]
                  | "if" Exp "then" Stmt "else" Stmt [strict(1), klabel
                  ('if_then_else_)]
                  | "while" Exp "do" Stmt [klabel('while_do_)]
                  | "{" Stmt "}" [bracket, klabel('{_})]
                  > "L1Stmt" Id ":" Stmt

    syntax Code ::= Exp
                  | Stmt
                  > "L1Code" Id ":" Code

    rule <k1> 'L1Exp_:_(_:Id,, GeneratedFreshVar0:Exp) => GeneratedFreshVar0
       ...</k1>

    rule <k1> 'L1Stmt_:_(_:Id,, GeneratedFreshVar1:Stmt) =>
      GeneratedFreshVar1 ...</k1>

    rule <k1> 'L1Code_:_(_:Id,, GeneratedFreshVar2:Code) =>
      GeneratedFreshVar2 ...</k1>

    syntax KResult ::= Int
                     | Bool

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

    rule <k1> 'L1Exp_:_(_:Id,, GeneratedFreshVar3:Exp) => GeneratedFreshVar3
       ...</k1>

    rule <k1> 'L1Stmt_:_(_:Id,, GeneratedFreshVar4:Stmt) =>
      GeneratedFreshVar4 ...</k1>

    rule <k1> 'L1Code_:_(_:Id,, GeneratedFreshVar5:Code) =>
      GeneratedFreshVar5 ...</k1>

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
                  > "L2FExp" Id ":" FExp

    syntax Val ::= "lambda" Id "." FExp [binder, klabel('lambda_._)]
                 | Int
                 | Bool
                 > "L2Val" Id ":" Val

    rule <k2> 'L2FExp_:_(_:Id,, GeneratedFreshVar6:FExp) =>
      GeneratedFreshVar6 ...</k2>

    rule <k2> 'L2Val_:_(_:Id,, GeneratedFreshVar7:Val) => GeneratedFreshVar7
       ...</k2>

    syntax KResult ::= Val

    rule <k2> I1:Int f+ I2:Int => I1 +Int I2 ...</k2>

    rule <k2> I1:Int f- I2:Int => I1 -Int I2 ...</k2>

    rule <k2> I1:Int f== I2:Int => I1 ==Int I2 ...</k2>

    rule <k2> I1:Int f< I2:Int => I1 <Int I2 ...</k2>

    rule <k2> if true then S1:FExp else _:K => S1 ...</k2>

    rule <k2> if false then _:K else S2:FExp => S2 ...</k2>

    rule <k2> (lambda X:Id . E:FExp) V:Val => E [ V / X ] ...</k2>

    rule <k2> fix X:Id E:FExp => E [ (fix X E) / X ] ...</k2>

    rule <k2> 'L2FExp_:_(_:Id,, GeneratedFreshVar8:FExp) =>
      GeneratedFreshVar8 ...</k2>

    rule <k2> 'L2Val_:_(_:Id,, GeneratedFreshVar9:Val) => GeneratedFreshVar9
       ...</k2>

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
                        $PGM2:K
                    </k2>
                </t2>
            </second>
        </aggregation>

      syntax KResult ::= "Success1" | "Success2"

      rule <k1> R:KResult => Success1 </k1> <k2> R:KResult => Success2 </k2>

endmodule
