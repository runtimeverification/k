// Copyright (c) 2014 K Team. All Rights Reserved.
require "../simple-untyped.k"

module SUM-SPEC
  imports SIMPLE-UNTYPED

/* function specification */
rule
<T>
    <threads>
        <thread>
            <k>
                sum(X:Int) => ?Y:Int
            </k>
            <control>
                <fstack>
                    _:List
                </fstack>
                <xstack>
                    _:List
                </xstack>
            </control>
            <env>
                sum |-> 0
            </env>
            <holds>
                .Map
            </holds>
            <id>
                0
            </id>
        </thread>
    </threads>
    <genv>
        sum |-> 0
    </genv>
    <store>
        0 |-> lambda ( x , { var y ; (y = 0) ; while ( (x > 0) ) { (y = (y
           + x)) ; (x = (x - 1)) ; } return y; } )
        (.Map => ?M:Map)
    </store>
    <busy>
        .Set
    </busy>
    <terminated>
        .Set
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
requires X >=Int 0
ensures ?Y ==Int (X *Int (X +Int 1)) /Int 2

/* loop invariant */
rule
<T>
    <threads>
        <thread>
            <k>
                while ( (x > 0) ) { (y = y + x) ; (x = x - 1) ; }
              =>
                .K
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
                y |-> Ly:Int
            ...</env>
            <holds>
                _:Map
            </holds>
            <id>
                _:Int
            </id>
        </thread>
    </threads>
    <genv>
        _:Map
    </genv>
    <store>...
        Lx |-> (X1:Int => 0)
        Ly |-> (Y1:Int => ?Y2:Int)
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
requires X1 >=Int 0
ensures ?Y2 ==Int Y1 +Int (X1 *Int (X1 +Int 1)) /Int 2
endmodule
