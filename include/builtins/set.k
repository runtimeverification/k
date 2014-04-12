// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "k-equal.k"
require "int.k"


module SET
  imports K-EQUAL-HOOKS
  imports INT-HOOKS

 /*@ \section{Description} The Set construct behaves like a mathematical
  set: it is a collection of unique items. The builtin \K Set offers support
  for some common set operations.
  (TODO: How does one add an element to a Set? How does one remove an element
  from a set? What is the difference between a Set and a MySet? What does this
  matter to the user?)
 */

  /*@ Construct a set from the union of two different sets (A $\cup$ B): */
  syntax Set ::= Set Set      [left, function, hook(Set:__), klabel('_Set_)]
  /*@ Construct an empty Set: */
  syntax Set ::= ".Set"       [function, hook(Set:.Set)]
  /*@ TODO: I don't know what this does. Construct a set of one element? Is this
   used to add elements to Sets? I never figured out how to add elements to
   Sets in 422; I actually once used Lists just to avoid having to. */
  syntax Set ::= SetItem(K)   [function, hook(Set:SetItem)]

  /*@ Get the difference of two sets: */
  syntax Set ::= Set "-Set" Set   [function, hook(Set:difference), latex({#1}-_{\it Set}{#2})]
//  rule (SetItem(K:K) S1:Set) -Set S2:Set => S1 -Set S2

//  when K in S2
//  rule (SetItem(K:K) S1:Set) -Set S2:Set => SetItem(K) (S1 -Set S2)
//  when notBool(K in S2)
//  rule .Set -Set _:Set => .Set

  /* set difference axioms */
//  rule S1:Set -Set (SetItem(K:K) S2:Set) => S1 -Set S2
//  when notBool(K in S1)
//  rule S:Set -Set .Set => S

  /*@ Construct a Set consisting of the intersection of two sets (A $\cap$ B):*/
  syntax Set ::= intersectSet(Set, Set)   [function]
//  rule intersectSet(S1:Set, S2:Set) => S1 -Set (S1 -Set S2)

  /*@ Test set inclusion ($S_1 \subseteq S_2 $): */
  syntax Bool ::= Set "<=Set" Set   [function, hook(Set:inclusion)]

  /*@ Test element membership in a set ($a \in A$): */
  syntax Bool ::= K "in" Set    [function, hook(Set:in)]
//  rule K1:K in SetItem(K2:K) S:Set => K1 =K K2 orBool K1 in S
//  rule _ in .Set => false

  /*@ Get the cardinality of a set (|A|) :*/
  syntax Int ::= size(Set)   [function, hook(Collection:size)]
//  rule size(SetItem(_) S:Set) => 1 +Int size(S)
//  rule size(.Set) => 0
endmodule

