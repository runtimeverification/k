// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../simple-untyped.k"

module HEAD-SPEC
  imports SIMPLE-UNTYPED

rule
<T>
    <threads>
        <thread>
            <k>
               head(x) => Y:Int
            ...</k>
            <control>
                <fstack>
                   _:List
                </fstack>
                <xstack>
                   _:List
                </xstack>
            </control>
            <env>...
                head |-> 0
                x |-> Lx:Int
            ...</env>
            <holds>
                .Map
            </holds>
            <id>
                0
            </id>
        </thread>
    </threads>
    <genv>
        head |-> 0
        x |-> Lx
    ...</genv>
    <store>
        0 |-> lambda ( x , { return (x [ 0 ]) ; } )
        Lx |-> X1:Val
        list(X1)(Y :: A:Seq)
        (.Map => ?M:Map)
    ...</store>
    <busy>
        _:Set
    </busy>
    <terminated>
        _:Set
    </terminated>
    <in>
        _:List
    </in>
    <out>
        _:List
    </out>
    <nextLoc>
        N1:Int => ?N2:Int
    </nextLoc>
</T>

endmodule
