// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "builtins/list.k"

module TEST
  imports LIST
  configuration <k> print(7) </k> <out stream="stdout"> .List </out>
  syntax KItem ::= print(Int)
  rule <k> print(I:Int) => .K ...</k> <out>... .List => ListItem(I) </out>
  rule
    ListItem(_:KItem)
    ListItem(#buffer(S:String => S +String Int2String(I)))
    (ListItem(I:Int) => .List)
    L:List
  [stdout]
endmodule

