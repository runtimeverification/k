// Copyright (c) 2018-2019 K Team. All Rights Reserved.

requires "domains.k"

module A

  imports DOMAINS

  syntax MyMap [smt-prelude]
  syntax Key [smt-prelude]
  syntax Val [smt-prelude]

  syntax MyMap ::= storeMyMap(MyMap, Key, Val) [function, smtlib(store)]
  syntax Val ::= selectMyMap(MyMap, Key) [function, smtlib(select)]

  syntax MyMap ::= ".MyMap"

  syntax Int ::= h(Int) [function, smtlib(h), smt-prelude]

  configuration <T>
    <k> $PGM:Term </k>
    <m> .MyMap </m>
    <f> 0 </f>
  </T>

  syntax Term ::= insert(Key, Val)
                | lookup(Key)

  rule <k> insert(K,V) => . ... </k>
       <m> M:MyMap => storeMyMap(M,K,V) </m>

  rule <k> lookup(K) => selectMyMap(M,K) ... </k>
       <m> M:MyMap </m>

endmodule
