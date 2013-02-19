require "builtins/k-equal.k"


module K-FUNCTIONAL-VISITOR
  imports K-EQUAL-HOOKS
  imports BUILTIN-HOOKS

  syntax KList ::= "$visit" "(" KList "," KLabel "," KList "," KLabel "," KList ")"    [function]
/*
                 | "$visit" "(" KList "," KLabel "," KList "," KLabel ")"              [function]
                 | "$visit" "(" KList "," KLabel "," KLabel "," KList ")"              [function]
                 | "$visit" "(" KList "," KLabel "," KLabel ")"                        [function]
                 | "$visit" "(" KList "," KLabel "," KList ")"                         [function]
                 | "$visit" "(" KList "," KLabel ")"                                   [function]
*/
  syntax K ::= "#visit" "(" K "," KLabel "," KList "," KLabel "," KList ")"    [function]
             | "#visit" "(" K "," KLabel "," KList "," KLabel ")"              [function]
             | "#visit" "(" K "," KLabel "," KLabel "," KList ")"              [function]
             | "#visit" "(" K "," KLabel "," KLabel ")"                        [function]
             | "#visit" "(" K "," KLabel "," KList ")"                         [function]
             | "#visit" "(" K "," KLabel ")"                                   [function]

/*
  rule
    #visit(K:K,
           VisitLabel:KLabel,
           VisitList:KList,
           IfLabel:KLabel,
           IfList:KList)
  =>
    $visit((K,,.KList), VisitLabel, VisitList, IfLabel, IfList)
*/

  rule
    #visit(K:K, VisitLabel:KLabel, VisitList:KList, IfLabel:KLabel)
  =>
    #visit(K, VisitLabel, VisitList, IfLabel, .KList)
  rule
    #visit(K:K, VisitLabel:KLabel, IfLabel:KLabel, IfList:KList)
  =>
    #visit(K, VisitLabel, .KList, IfLabel, IfList)
  rule
    #visit(K:K, VisitLabel:KLabel, IfLabel:KLabel)
  =>
    #visit(K, VisitLabel, .KList, IfLabel, .KList)
  rule
    #visit(K:K, VisitLabel:KLabel, VisitList:KList)
  =>
    #visit(K, VisitLabel, VisitList, $visitTrue, .KList)
  rule
    #visit(K:K, VisitLabel:KLabel)
  =>
    #visit(K, VisitLabel, .KList)

  syntax KLabel ::= "$visitTrue"
  rule $visitTrue(_:KList) => true    [anywhere]

  rule
    $visit(K1,,K2,,KList:KList,
           VisitLabel:KLabel,
           VisitList:KList,
           IfLabel:KLabel,
           IfList:KList)
  =>
    $visit(K1, VisitLabel, VisitList, IfLabel, IfList),,
    $visit(K2, VisitLabel, VisitList, IfLabel, IfList),,
    $visit(KList, VisitLabel, VisitList, IfLabel, IfList)
  rule $visit(.KList, _:KLabel, _:KList, _:KLabel, _:KList) => .KList

  rule
    #visit(K1 ~> K2,
           VisitLabel:KLabel,
           VisitList:KList,
           IfLabel:KLabel,
           IfList:KList)
  =>
    #visit(K1, VisitLabel, VisitList, IfLabel, IfList)
    ~> #visit(K2, VisitLabel, VisitList, IfLabel, IfList)
  when K1 =/=K .K andBool K2 =/=K .K
  rule #visit(.K, _:KLabel, _:KList, _:KLabel, _:KList) => .K
  
  rule
    #visit(KLabel:KLabel(KList:KList),
           VisitLabel:KLabel,
           VisitList:KList,
           IfLabel:KLabel,
           IfList:KList)
  =>
    #if IfLabel(KLabel:KLabel(KList:KList),,IfList) ==K true #then
      VisitLabel(KLabel:KLabel(KList:KList),,VisitList)
    #else
      KLabel($visit(KList, VisitLabel, VisitList, IfLabel, IfList))
    #fi
endmodule

