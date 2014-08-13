// Copyright (c) 2014 K Team. All Rights Reserved.
require "../simple-untyped.k"

module HEAD-SPEC
  imports SIMPLE-UNTYPED

rule
<T>
    <threads>
        <thread>
            <k>
               return (x [ 0 ]) ; => return Y:Int ;
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
        _:Map
    </genv>
    <store>...
        Lx |-> X1:Val
        list(X1)(Y :: A:Seq)
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
        _:Int
    </nextLoc>
</T>

endmodule
