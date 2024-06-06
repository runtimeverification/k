// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module OTHER-MODULE
  imports INT

  configuration
    <freshGroup>
      <freshMember0> !_C:Int </freshMember0>
      <freshMember1> !_:Int  </freshMember1>
    </freshGroup>

endmodule

module TEST-SYNTAX

  syntax Program ::= "start" | "done"

endmodule

module TEST
  imports TEST-SYNTAX
  imports BOOL
  imports INT
  imports LIST
  imports OTHER-MODULE

  configuration
    <k> $PGM:Program </k>
    <fresh0> !_A:Int </fresh0>
    <fresh1> !_A:Int </fresh1>
    <fresh2> !_B:Int </fresh2>
    <fresh3> !_:Int  </fresh3>
    <freshGroup/>

  syntax KItem ::= assertEqual( List )
                 | assertEqual( Int, List )
                 | assertNotEqual( List )
                 | assertNotEqual( Int, List )

  rule assertEqual( .List ) => .K
  rule assertEqual( ListItem(X:Int) REST )  => assertEqual( X, REST ) ~> assertEqual( REST )

  rule assertEqual( _, .List ) => .K
  rule assertEqual( X, ListItem( X ) REST ) => assertEqual( X, REST )

  rule assertNotEqual( .List ) => .K
  rule assertNotEqual( ListItem(X:Int) REST )  => assertNotEqual( X, REST ) ~> assertNotEqual( REST )

  rule assertNotEqual( _, .List ) => .K
  rule assertNotEqual( X, ListItem( Y ) REST ) => assertNotEqual( X, REST ) requires X =/=Int Y

  rule start => !_A:Int

  rule <k> A:Int
        => assertEqual( ListItem( B ) ListItem( C ) )
        ~> assertNotEqual( ListItem( A ) ListItem( B ) ListItem( D ) ListItem( E ) ListItem( F ) ListItem( G ) )
        ~> done
           ...
       </k>
  <fresh0> B </fresh0>
  <fresh1> C </fresh1>
  <fresh2> D </fresh2>
  <fresh3> E </fresh3>
  <freshGroup>
    <freshMember0> F </freshMember0>
    <freshMember1> G </freshMember1>
  </freshGroup>

endmodule
