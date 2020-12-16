// Copyright (c) 2018-2019 K Team. All Rights Reserved.

requires "a.k"

module A-SPEC

  imports A

  claim <k> insert(KEY,VALUE) ~> lookup(KEY) => VALUE ... </k>
        <m> MAP:MyMap => ?_:MyMap </m>
        <f> 0 => 1 </f>

  claim <k> insert(KEY1,VALUE1)
         ~> insert(KEY2,VALUE2)
         ~> lookup(KEY1) => VALUE1 ... </k>
        <m> MAP:MyMap => ?_:MyMap </m>
        <f> 0 => 1 </f>
        requires KEY1 =/=K KEY2
         andBool VALUE1 =/=K VALUE2

  claim <f> 0 => 1 </f>
        requires h(0) ==Int h(1)
        [trusted]

endmodule
