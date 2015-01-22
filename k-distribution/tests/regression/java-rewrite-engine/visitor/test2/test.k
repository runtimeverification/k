// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "modules/k-functional-visitor.k"

module TEST
  imports K-FUNCTIONAL-VISITOR

  syntax PseudoCodes ::= PseudoCode PseudoCodes
                       | PseudoCode
  syntax PseudoCode  ::= "Let" Id "=" K ";" [seqstrict(2)]
                       | "Return" K ";" [seqstrict(1)]

  rule PC:PseudoCode PCs:PseudoCodes => PC ~> PCs

  rule Let X:Id = V:KResult; ~> PCs:PseudoCodes
    => #visit(PCs, '@Replace`(_`,_`), V, '_==K_, X)

  syntax KItem ::= "@Replace" "(" K "," K ")" [function]
  rule @Replace(_, K) => K

  syntax KResult ::= Val

  syntax Exp ::= Val
               | Id

  syntax Var ::= String
  syntax Val ::= Int

  syntax Val ::= "@desc" "(" Map ")"

  syntax Exp ::= Exp "." Var [function]
  rule @desc(X |-> V:Val _) . X => V

  syntax KItem ::= "start"

  syntax Id ::= "$desc"
  rule start
    => Let $desc = foo;
       Return $desc."x";

  syntax KItem ::= "foo"
  rule foo => @desc("x" |-> 1 "y" |-> 2)

endmodule
