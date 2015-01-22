// Copyright (c) 2013-2015 K Team. All Rights Reserved.
require "builtins/k-equal.k"


module K-FUNCTIONAL-VISITOR
  imports K-EQUAL-HOOKS
  imports BUILTIN-HOOKS

  /*
   * Generic K-AST visitor
   *   #visit(K, VisitLabel, VisitList, IfLabel, IfList)
   * where
   *   K           K representation of the AST
   *   VisitLabel  KLabel of the function applied to an AST node
   *   VisitList   KList of additional arguments for VisitLabel
   *   IfLabel     KLabel of the predicate guard for VisitLabel
   *   IfList      KList of additional arguments for IfLabel
   * #visit traverses the AST K top-down int the following way: for each node K'
   * if IfLabel(K',,IFList) holds then replace K' with VisitLabel(K',,VisitList)
   * otherwise recurse on the children of K'.
   */
  syntax KItem ::= "#visit" "(" K "," KLabel "," KList "," KLabel "," KList ")"   [function, hook(Visitor:visit), impure]

  /*
   * Particular forms of #visit (default argument KList is .KList, default
   * KLabel predicate is '$visitTrue)
   */
  syntax KItem ::= "#visit" "(" K "," KLabel "," KList "," KLabel ")"   [function]
                 | "#visit" "(" K "," KLabel "," KLabel "," KList ")"   [function]
                 | "#visit" "(" K "," KLabel "," KLabel ")"             [function]
                 | "#visit" "(" K "," KLabel "," KList ")"              [function]
                 | "#visit" "(" K "," KLabel ")"                        [function]

  /*
   * #visitAll of a KList (first argument) applies #visit to each element of the
   * list.
   */
  syntax KList ::= "#visitAll" "(" KList "," KLabel "," KList "," KLabel "," KList ")"    [function]
                 | "#visitAll" "(" KList "," KLabel "," KList "," KLabel ")"              [function]
                 | "#visitAll" "(" KList "," KLabel "," KLabel "," KList ")"              [function]
                 | "#visitAll" "(" KList "," KLabel "," KLabel ")"                        [function]
                 | "#visitAll" "(" KList "," KLabel "," KList ")"                         [function]
                 | "#visitAll" "(" KList "," KLabel ")"                                   [function]

  /*
   * Reduce uses of particular forms of #visit to the use of the most general
   * form.
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
    #visit(K, VisitLabel, VisitList, '$visitTrue, .KList)
  rule
    #visit(K:K, VisitLabel:KLabel)
  =>
    #visit(K, VisitLabel, .KList, '$visitTrue, .KList)

  /*
   * Reduce uses of particular forms of #visitAll to the use of the most general
   * form.
   */
  rule
    #visitAll(KList:KList, VisitLabel:KLabel, VisitList:KList, IfLabel:KLabel)
  =>
    #visitAll(KList, VisitLabel, VisitList, IfLabel, .KList)
  rule
    #visitAll(KList:KList, VisitLabel:KLabel, IfLabel:KLabel, IfList:KList)
  =>
    #visitAll(KList, VisitLabel, .KList, IfLabel, IfList)
  rule
    #visitAll(KList:KList, VisitLabel:KLabel, IfLabel:KLabel)
  =>
    #visitAll(KList, VisitLabel, .KList, IfLabel, .KList)
  rule
    #visitAll(KList:KList, VisitLabel:KLabel, VisitList:KList)
  =>
    #visitAll(KList, VisitLabel, VisitList, '$visitTrue, .KList)
  rule
    #visitAll(KList:KList, VisitLabel:KLabel)
  =>
    #visitAll(KList, VisitLabel, .KList, '$visitTrue, .KList)

  /*
   * Default predicate guard (always true)
   */
  // TODO(AndreiS): fix this declaration; cannot declare a function
  // with variable number of arguments
  syntax Bool ::= "$visitTrue" "(" KItem ")"   [function, klabel('$visitTrue)]
  rule '$visitTrue(_:KList) => true

  /*
   * #visitAll applies #visit to each element of the KList (first argument).
   */
  rule
    #visitAll(K:K,,KList:KList,
           VisitLabel:KLabel,
           VisitList:KList,
           IfLabel:KLabel,
           IfList:KList)
  =>
    #visit(K, VisitLabel, VisitList, IfLabel, IfList),,
    #visitAll(KList, VisitLabel, VisitList, IfLabel, IfList)
  rule #visitAll(.KList, _:KLabel, _:KList, _:KLabel, _:KList) => .KList

  /*
   * #visit applied to a "~>" sequence of K items (first argument) reduces to
   * #visit applied to each K item.
   */
  // TODO(AndreiS): replace K1 and K2 with KI:KItem and K:K
  rule
    #visit(K1:K ~> K2:K,
           VisitLabel:KLabel,
           VisitList:KList,
           IfLabel:KLabel,
           IfList:KList)
  =>
    #visit(K1, VisitLabel, VisitList, IfLabel, IfList)
    ~> #visit(K2, VisitLabel, VisitList, IfLabel, IfList)
  when K1 =/=K .K andBool K2 =/=K .K
  rule #visit(.K, _:KLabel, _:KList, _:KLabel, _:KList) => .K

  /*
   * #visit applied to an AST node (a KLabel applies to a KList) either
   * transforms the node or reduces to #visit applied to its children.
   */
  rule
    #visit(KLabel:KLabel(KList:KList),
           VisitLabel:KLabel,
           VisitList:KList,
           IfLabel:KLabel,
           IfList:KList)
  =>
    #if IfLabel(KLabel(KList),,IfList) ==K true #then
      VisitLabel(KLabel(KList),,VisitList)
    #else
      KLabel(#visitAll(KList, VisitLabel, VisitList, IfLabel, IfList))
    #fi
endmodule

