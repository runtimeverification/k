require "builtins/list.k"

module TEST
  imports LIST 
  configuration <k> print(7) </k> <out stream="stdout"> .MyList </out>
  syntax K ::= print(Int)
  rule <k> print(I:Int) => .K ...</k> <out>... .MyList => MyListItem(I) </out>
  rule MyListItem(_:KItem), MyListItem(#buffer(S:String => S +String Int2String(I))),
    (MyListItem(I:Int) => .MyList), L:MyList [stdout]
endmodule
