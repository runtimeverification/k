// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module LENGTH-RECURSIVE-SPEC
  imports KERNELC

rule [loop-inv]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    if (x == NULL) return 0 ;
    return 1 + length_recursive(x -> next);
  =>
    return tv(int, len(A)) ; ~> _:K // YilongL: ` ~> _:K` is neccessary to prove the base case
  ...</k>
  <env>...
    x |-> tv ( struct listNode * * , object(B:Int))
  ...</env>
  <heap>...
    object(B) |-> tv (struct listNode *, LP:Pointer)
    list(LP)(A:Seq)
  ...</heap>

rule [func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    length_recursive(tv(struct listNode *, LP:Pointer))
  =>
    tv(int, len(A))
  ...</k>
  <heap>...
    list(LP)(A:Seq)
  ...</heap>

endmodule
