module CHECKRECORDPRODDUPLICATELABELS-SYNTAX
endmodule

module CHECKRECORDPRODDUPLICATELABELS
  imports CHECKRECORDPRODDUPLICATELABELS-SYNTAX
  imports INT
  imports MAP
  imports LIST
  syntax StateCell ::= Int
syntax StateCell ::= invariantStateFull(
      p1:Int,
      p2:Int,
      p3:Int,
      p4:Int,
      p5:Int,
      p6:Int,
      P7:Int,
      p8:Int,
      p9:Int,
      p10:Int,
      P11:Int,
      p12:Int,
      p13:Int,
      p14:Int,
      p15:Int,
      p16:Int,
      numUsers:Int,
      userIdToAddress:Map,
      addressToUserId:Map,
      numBoardMembers:Int,
      numProposers:Int,
      userIdToRole:Map,
      quorum:Int,
      actionLastIndex:Int,
      actionData:Map,
      actionSigners:Map,
      callerAddress:KItem,
      stack:Int,
      variables:Map,
      performedActions:List) // 30 params
 rule invariantStateFull(... p1:X, p1:Y) => 1 // duplicate keys here, rest should be fine
 rule invariantStateFull(... p2:X, numUsers:_Gen0, p2:Y) => 1 // duplicate keys here, rest should be fine
 rule invariantStateFull(... numUsers:_X, stack:_Y, quorum:_Z, variables:_P) => 1
 rule invariantStateFull(... quorum:_Z, variables:_P, numUsers:_X, stack:_Y, p1:_Q) => 1
 rule invariantStateFull(... numUsers:_X) ~> invariantStateFull(...) => 1

 syntax StateCell ::= abc(one:Int)
 rule abc(... one:X) => 1

 syntax Mix ::= Int
 syntax Mix ::= "a" p1:Int
                "b" p2:Int
                "c" p3:Int
                "d" p4:Int
                "e" p5:Int
                "f" p6:Int
                "g" p7:Int
                "h" p8:Int
                "i" p9:Int
                "j" p10:Int
                "k" p11:Int
                "l" p12:Int
                "m" p13:Int
                "n" p14:Int
                "o" p15:Map
                "p" p16:Int
                "q" p17:Int
                "r" p18:Int
                "s" p19:Int
                "t" p20:KItem
                "u" p21:Int
                "v" p22:Int
                "w" p23:Int
                "x" p24:Int
                "y" p25:Int
                "z" p26:Int
 rule a _ b _ c _ d _ e _ f _ g _ h _ i _ j _ k _ l _ m _ n _ o _ p _ q _ r _ s _ t _ u _ v _ w _ x _ y _ z _ => 1
endmodule
