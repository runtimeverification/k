// Copyright (c) 2014 K Team. All Rights Reserved.

module ISSUE
  syntax KItem ::= "a" | "b"
  configuration <k> a ~> b </k> <set> SetItem(1) </set>
                <out stream="stdout"> .List </out>

  rule <k> a => . ...</k> <set>... .Set => SetItem(?I:Int) ...</set>

  rule <k> b => . ...</k> <set> S:Set </set> <out>... .List => ListItem("success") </out>
    when 1 in S
endmodule

