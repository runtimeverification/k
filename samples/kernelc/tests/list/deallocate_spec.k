// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module DEALLOCATE-SPEC
  imports KERNELC

rule [loop-inv]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while ( (x != tv ( void * , null )) ) { struct listNode * y ;
    y = (x -> next) ; (free ( x )) ; x = y ; }
  =>
    .K
  ...</k>
  <env>...
    x |-> tv(struct listNode * *, object(B:Int))
  ...</env>
  <heap>...
    object(B) |-> tv (struct listNode *, LP:Pointer => null)
    (list(LP)(_:IntSeq) => .Map)
  ...</heap>

rule [func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    deallocate(tv(struct listNode *, LP:Pointer))
  =>
    tv(void, undef)
  ...</k>
  <heap>...
    list(LP)(_:IntSeq) => .Map
  ...</heap>

endmodule
