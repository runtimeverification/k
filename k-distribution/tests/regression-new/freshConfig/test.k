// Copyright (c) K Team. All Rights Reserved.
module OTHER-MODULE
  imports INT

configuration
  <freshGroup>
    <freshMember0> !_:Int </freshMember0>
    <freshMember1> !_:Int </freshMember1>
    <freshMember2> !_A:Int </freshMember2>
    <freshMember3> !_A:Int </freshMember3>
    <freshMember4> !_B:Int </freshMember4>
  </freshGroup>

endmodule

module TEST
  imports INT
  imports OTHER-MODULE

  syntax Program ::= "start"

configuration
    <k> $PGM:Program </k>
    <fresh0> !_:Int </fresh0>
    <fresh1> !_:Int </fresh1>
    <fresh2> !_C:Int </fresh2>
    <fresh3> !_C:Int </fresh3>
    <fresh4> !_D:Int </fresh4>
    <freshGroup/>

    rule start => !_A:Int

endmodule
