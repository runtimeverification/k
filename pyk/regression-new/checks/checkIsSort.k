// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CHECKISSORT-SYNTAX
  imports BOOL-SYNTAX
  imports BASIC-K

  syntax Foo ::= Blah(Bool)

  syntax Bool ::= isNonAddr(KItem)  [function]
                | isNotASort(KItem) [function]
                | isNonAddr(Foo)    [function]
                | isnonaddr(KItem)  [function]
                | isNonAddr ( KItem , KItem ) [function]
                | isFoo(Foo) [function]

  syntax NonAddr ::= nonAddr(KItem)
endmodule

module CHECKISSORT
  imports CHECKISSORT-SYNTAX
endmodule
