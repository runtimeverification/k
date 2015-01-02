// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "modules/pattern-matching.k"

module TEST
  imports PATTERN-MATCHING

  syntax Variable ::= Name
  syntax Name ::= Token{"x0"} | Token{"x1"} | Token{"x2"}
  syntax Exp ::= Name | "[" Exps "]" | "[" Exps "|" Exp "]" | Val
  syntax Exps  ::= List{Exp,","}  [strict]
  syntax Val ::= Integer
  syntax Vals ::= List{Val,","}

//@ Multiple-head list patterns desugar into successive one-head patterns:

  rule [E:Exp,Es|T] => [E|[Es|T]]  when Es =/=K .Exps        [macro]

// YilongL: user-defined decomposing function
//  rule decomposeMatching(([H:Exp|T:Exp] => H,T),
//                         ([V:Val,Vs:Vals] => V,[Vs]))
  rule decomposeMatching([H:Exp|T:Exp], [V:Val,Vs:Vals]) => decomposeMatching((H,T), (V,[Vs]))

  syntax Integer ::= "int(" Int ")"

  // testing generic pattern decomposing
  rule 0 => isMatching(x0,,int(2),,x1,,int(4),,x2, int(1),,int(2),,int(3),,int(4),,int(5)) // true
  rule 1 => isMatching(x0,,int(2),,x1,,int(4),,x2, int(1),,int(2),,int(3),,int(5),,int(5)) // false
  rule 2 => isMatching(x0,,int(2),,x1,,int(4),,x0, int(1),,int(2),,int(3),,int(4),,int(5)) // non-linear pattern
  rule 3 => getMatching(x0,,int(2),,x1,,int(4),,x2, int(1),,int(2),,int(3),,int(4),,int(5))

  // testing user-defined decomposing function
  rule 4 => isMatching([x0 | [int(2) | [x1 | [int(4) | x2]]]], [int(1) | [int(2) | [int(3) | [int(4) | int(5)]]]]) // true
  rule 5 => isMatching([x0 | [int(2) | [x1 | [int(4) | x2]]]], [int(1) | [int(2) | [int(3) | [int(5) | int(5)]]]]) // false
  rule 6 => isMatching([x0 | [int(2) | [x1 | [int(4) | x0]]]], [int(1) | [int(2) | [int(3) | [int(4) | int(5)]]]]) // non-linear pattern
  rule 7 => getMatching([x0 | [int(2) | [x1 | [int(4) | x2]]]], [int(1) | [int(2) | [int(3) | [int(4) | int(5)]]]])

  // testing multiple-head list patterns
  rule 8 => isMatching([x0, int(2), x1, int(4) | x2], [int(1), int(2), int(3), int(4), int(5)]) // true
  rule 9 => isMatching([x0, int(2), x1, int(4) | x2], [int(1), int(2), int(3), int(5), int(5)]) // false
  rule 10 => isMatching([x0, int(2), x1, int(4) | x0], [int(1), int(2), int(3), int(4), int(5)]) // non-linear pattern
  rule 11 => getMatching([x0, int(2), x1, int(4) | x2], [int(1), int(2), int(3), int(4), int(5)])

  configuration
    <k> $PGM:K </k>

endmodule

