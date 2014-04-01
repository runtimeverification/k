// Copyright @ 2012-2014.  K Team.  All Rights Reserved.

require "builtins/k-equal.k"

module K-VISITOR
  imports K-EQUAL-HOOKS
  imports BUILTIN-HOOKS

  syntax KItem  ::= #label(KLabel)       // Should be eventually builtin

  syntax KLabel ::= "#visit"
  syntax KLabel ::= "#visitor"
  syntax KLabel ::= "#visited"

// #visitor takes an action and a predicate, and applies the action on each
// visited KItem that satisfies the predicate.  The action is typically a
// curried funtion, and the predicate is just a function (encoded as a label item).
  rule #visit(L:KLabel(Kl:KList),, #visitor(A:KLabel(Kla:KList),, #label(P)))
    => #if P(L(Kl)) ==K true
       #then A(Kla,,L(Kl))
       #else #visiting.kapp(#label(L),, #visit(Kl,, #visitor(A(Kla),, #label(P))))
       #fi                                                                                     [structural]
  rule #visit(Vz:KItem)                      => #visited(.KList)                               [structural]
  rule #visit(K:K,, NeKl:KList,, Vz:KItem)   => #visiting.klist(#visit(K,,Vz),,#visit(NeKl,,Vz))
    when NeKl =/=KList .KList                                                                  [structural]
  rule #visit(K:KItem ~> Kr,, Vz:KItem)      => #visiting.kseq(#visit(K,,Vz),,#visit(Kr,,Vz))
    when Kr =/=K .K                                                                            [structural]

  syntax KLabel ::= "#visiting.kapp"     // [strict(2)]
  syntax KLabel ::= "#visiting.kseq"     // [strict]
  syntax KLabel ::= "#visiting.klist"    // [strict]

// Due to bugs, the strictness attributes above don't work, so we need the following
  context #visiting.kapp(_:KItem,,HOLE)  // the first argument should be a KToken
  context #visiting.klist(_,,HOLE)
  context #visiting.klist(HOLE,,_)
  context #visiting.kseq(_,,HOLE)
  context #visiting.kseq(HOLE,,_)

// Traverse the visited term bottom up and mark everything visited.
  rule #visiting.kapp(#label(L),,#visited(Kl:KList)) => #visited(L(Kl))                        [structural]
  rule #visiting.klist(#visited(Kl:KList),,#visited(Kl':KList)) => #visited(Kl,,Kl')           [structural]
  rule #visiting.kseq(#visited(K1:K),,#visited(K2:K)) => #visited(K1 ~> K2)                    [structural]
endmodule
