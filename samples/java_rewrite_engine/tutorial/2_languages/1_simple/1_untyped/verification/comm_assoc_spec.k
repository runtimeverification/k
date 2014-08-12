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
                comm_assoc(X:Int, Y:Int, Z:Int) => true
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
                f |-> 0 comm_assoc |-> 1
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
        f |-> 0 comm_assoc |-> 1
    </genv>
    <store>
        0 |-> lambda ( x, y , { return ((x + y) + (x * y)) ; } )
        1 |-> lambda ( x, y, t , { return (((f ( x, y )) == (f ( y, x ))) && ((f (
           x, (f ( y, t )) )) == (f ( (f ( x, y )), t )))) ; } )
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

endmodule
