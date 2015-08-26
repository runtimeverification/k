// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module INT-SET
  syntax IntSet ::= IntSet "U" IntSet           [function, left, smtlib(smt_set_cup)]
                  | ".IntSet"                   [function, smtlib(smt_set_emp)]
                  | "{" Int "}"                 [function, smtlib(smt_set_ele), klabel(smt_set_ele)]
                  | IntSet "-IntSet" IntSet     [function, smtlib(smt_set_dif)]
  syntax Bool ::= Int "inIntSet" IntSet         [function, smtlib(smt_set_mem)]
                | IntSet  "<IntSet" IntSet      [function, smtlib(smt_set_lt)]
                | IntSet "<=IntSet" IntSet      [function, smtlib(smt_set_le)]
  rule S:IntSet U .IntSet => S    [lemma]
  rule .IntSet U S:IntSet => S    [lemma]

  rule I:Int inIntSet (S1:IntSet U S2:IntSet)
    => (I inIntSet S1) orBool (I inIntSet S2)
    [lemma]
  rule _:Int inIntSet .IntSet => false                  [lemma]
  rule I1:Int inIntSet { I2:Int } => I1 ==K I2          [lemma]

  rule S:IntSet <IntSet (S1:IntSet U S2:IntSet)
    => (S:IntSet <IntSet S1:IntSet) andBool (S:IntSet <IntSet S2:IntSet)
    [lemma]
  rule (S1:IntSet U S2:IntSet) <IntSet S:IntSet
    => (S1:IntSet <IntSet S:IntSet) andBool (S2:IntSet <IntSet S:IntSet)
    [lemma]
  rule _:IntSet <IntSet .IntSet => true                 [lemma]
  rule .IntSet <IntSet _:IntSet => true                 [lemma]
  rule { I1:Int } <IntSet { I2:Int } => I1 <Int I2      [lemma]

  rule S:IntSet <=IntSet (S1:IntSet U S2:IntSet)
    => (S:IntSet <=IntSet S1:IntSet) andBool (S:IntSet <=IntSet S2:IntSet)
    [lemma]
  rule (S1:IntSet U S2:IntSet) <=IntSet S:IntSet
    => (S1:IntSet <=IntSet S:IntSet) andBool (S2:IntSet <=IntSet S:IntSet)
    [lemma]
  rule _:IntSet <=IntSet .IntSet => true                [lemma]
  rule .IntSet <=IntSet _:IntSet => true                [lemma]
  rule { I1:Int } <=IntSet { I2:Int } => I1 <=Int I2    [lemma]

  rule .IntSet -IntSet _:IntSet => .IntSet              [lemma]
endmodule

