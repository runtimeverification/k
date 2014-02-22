module PATTERN-MATCHING

// adapted from k-prelude.k
  syntax KItem ::= #myMap(MyMap)
  syntax Bool ::= #myIsMapInK(K)      [function]
  syntax MyMap ::= #myGetMapFromK(K)  [function]

  rule #myIsMapInK(#myMap(_)) => true
  rule #myIsMapInK(_) => false  [owise]  // YilongL: avoid partial function that gets stuck and fails the Java rewrite engine assertion
  rule #myGetMapFromK(#myMap(M:MyMap)) => M

/***********
  VISIBLE
***********/
// Tells if a matching exists
  syntax Bool ::= myIsMatching(KList, KList)            [function]
  rule myIsMatching(Ps:KList, Ks:KList)
    => #myIsMapInK(#myPatternMatch(Ps,Ks)) ==K true

// Gets the matching; call myIsMatching first, for safety
  syntax MyMap ::= myGetMatching(KList, KList)          [function]
  syntax KItem ::= #myPatternMatch(KList, KList)        [function]
  rule myGetMatching(Ps:KList, Ks:KList)
    => #myGetMapFromK(#myPatternMatch(Ps,Ks))

// Tells how to decompose pattern matching
  syntax KList ::= myDecomposeMatching(KList, KList)    [function]
  syntax KItem ::= myDoneDecomposeMatching(K, K)
// Here are some basic decomposition rules, but one can add more
//  rule myDecomposeMatching((L:KLabel(Ps:KList) => Ps), (L(Ks:KList) => Ks))
// TODO(Yilong): current impl. assumes that rewrite has been pushed to the top
  rule myDecomposeMatching(L:KLabel(Ps:KList), L(Ks:KList)) => myDecomposeMatching(Ps, Ks)
    when isVariable(L(Ps)) =/=K true
  rule myDecomposeMatching(P:Variable, K) => myDoneDecomposeMatching(P, K)
  rule myDecomposeMatching(P:K,,Ps:KList, K:K,,Ks:KList)
       => myDecomposeMatching(P, K),,myDecomposeMatching(Ps, Ks)
    //when Ps =/=KList .KList
    // TODO(YilongL): the current impl. of term inequality cannot handle non-ground arguments
    when notBool emptyKList(Ps)
  // rule myDecomposeMatching(.KList, .KList) => .KList
  // TODO(YilongL): builtins in Java rewrite engine may not be represented as KItem's
  rule myDecomposeMatching(Ks, Ks) => .KList  [owise]

// For example, one may add rules like the following in one's language
//  rule myDecomposeMatching(([P:Exp|T:Exp] => P,T),([V:Val,Vs:Vals] => V,[Vs]))

  syntax Bool ::= emptyKList(KList)  [function]
  rule emptyKList(.KList) => true
  rule emptyKList(K,,Ks) => false
/***********
  HIDDEN
***********/

  // Subsorting ids to variables for matching purposes.
  syntax Variable ::= Id

  syntax KItem ::= #myPatternMatch(KList, KList)   [function]
  rule #myPatternMatch(Ps:KList, Ks:KList)
    => #myPatternMatch1(myDecomposeMatching(Ps,Ks), .MyMap)

  syntax KItem ::= #myPatternMatch1(KList, MyMap)  [function]
  syntax KItem ::= "#nonlinearPatternError"
//  rule #myPatternMatch1((myDecomposeMatching(X:Variable,K:K) => .KList),,_,
//                      (M:MyMap, (.MyMap => X |-> K)))
  rule #myPatternMatch1(myDoneDecomposeMatching(X:Variable,K:K),,Ps, M:MyMap) // YilongL: use myDoneDecomposeMatching
    => #myPatternMatch1(.KList,,Ps, (M:MyMap, X |-> K))
    when notBool (X in keys(M))  // only linear patterns allowed for now
  rule #myPatternMatch1(myDoneDecomposeMatching(X:Variable,K:K),,Ps, M:MyMap)
    => #nonlinearPatternError
    when X in keys(M)  // TODO(YilongL): this side condition contains two function calls which can be combined into one instead
  rule #myPatternMatch1(.KList, M:MyMap) => #myMap(M)

  //rule #myPatternMatch1(_,_) => #nonlinearPatternError  [owise]

endmodule

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
//  rule myDecomposeMatching(([H:Exp|T:Exp] => H,T),
//                         ([V:Val,Vs:Vals] => V,[Vs]))
  rule myDecomposeMatching([H:Exp|T:Exp], [V:Val,Vs:Vals]) => myDecomposeMatching((H,T), (V,[Vs]))

  syntax Integer ::= "int(" Int ")"

  // testing generic pattern decomposing
  rule 0 => myIsMatching(x0,,int(2),,x1,,int(4),,x2, int(1),,int(2),,int(3),,int(4),,int(5)) // true
  rule 1 => myIsMatching(x0,,int(2),,x1,,int(4),,x2, int(1),,int(2),,int(3),,int(5),,int(5)) // false
  rule 2 => myIsMatching(x0,,int(2),,x1,,int(4),,x0, int(1),,int(2),,int(3),,int(4),,int(5)) // non-linear pattern
  rule 3 => myGetMatching(x0,,int(2),,x1,,int(4),,x2, int(1),,int(2),,int(3),,int(4),,int(5))

  // testing user-defined decomposing function
  rule 4 => myIsMatching([x0 | [int(2) | [x1 | [int(4) | x2]]]], [int(1) | [int(2) | [int(3) | [int(4) | int(5)]]]]) // true
  rule 5 => myIsMatching([x0 | [int(2) | [x1 | [int(4) | x2]]]], [int(1) | [int(2) | [int(3) | [int(5) | int(5)]]]]) // false
  rule 6 => myIsMatching([x0 | [int(2) | [x1 | [int(4) | x0]]]], [int(1) | [int(2) | [int(3) | [int(4) | int(5)]]]]) // non-linear pattern
  rule 7 => myGetMatching([x0 | [int(2) | [x1 | [int(4) | x2]]]], [int(1) | [int(2) | [int(3) | [int(4) | int(5)]]]])

  // testing multiple-head list patterns
  rule 8 => myIsMatching([x0, int(2), x1, int(4) | x2], [int(1), int(2), int(3), int(4), int(5)]) // true
  rule 9 => myIsMatching([x0, int(2), x1, int(4) | x2], [int(1), int(2), int(3), int(5), int(5)]) // false
  rule 10 => myIsMatching([x0, int(2), x1, int(4) | x0], [int(1), int(2), int(3), int(4), int(5)]) // non-linear pattern
  rule 11 => myGetMatching([x0, int(2), x1, int(4) | x2], [int(1), int(2), int(3), int(4), int(5)])

  configuration
    <k> $PGM:K </k>

endmodule
