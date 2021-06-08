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
 rule invariantStateFull(... p1:X, p1:Y) => 1
 rule invariantStateFull(... numUsers:_X, stack:_Y, quorum:_Z, variables:_P) => 1
 rule invariantStateFull(... numUsers:_X) ~> invariantStateFull(...) => 1
endmodule
