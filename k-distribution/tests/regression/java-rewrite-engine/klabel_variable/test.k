// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST
  syntax KItem ::= "foo" | "bar"
  rule Label:KLabel(List:KList) => 0
  when Label ==KLabel 'foo
endmodule

