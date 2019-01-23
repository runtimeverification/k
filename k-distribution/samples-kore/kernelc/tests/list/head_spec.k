// Copyright (c) 2014-2019 K Team. All Rights Reserved.
module HEAD-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k> head(tv(struct listNode *, LP:Pointer)) => tv(int, Y) ...</k>
  <heap>... list(LP)(ListItem(Y:Int) _:List) ...</heap>
endmodule
