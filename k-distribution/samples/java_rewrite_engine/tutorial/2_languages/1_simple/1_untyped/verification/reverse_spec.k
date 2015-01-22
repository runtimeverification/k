// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../simple-untyped.k"

module REVERSE-SPEC
  imports SIMPLE-UNTYPED

/*
rule
<T>
    <threads>
        <thread>
            <k>
               reverse(X:Int) => ?Y:Int
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
                reverse |-> 0
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
        reverse |-> 0
    </genv>
    <store>...
        0 |-> lambda ( x , { var y ; (y = 0) ; while ( (x != 0) ) { var t
          ; (t = (x [ 1 ])) ; ((x [ 1 ]) = y) ; (y = x) ; (x = t) ; } } )
        (list(X)(A:Seq) => list(?Y)(rev(A)))
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
*/

rule
<T>
    <threads>
        <thread>
            <k>
                while ( (x != 0) ) { (t = (x [ 1 ])) ; ((x [ 1 ]) = y) ; (y = x) ; (x = t) ; }
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
                t |-> Lt:Int
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
        Lx |-> (X1:Val => ?X2:Val)
        Ly |-> (Y1:Val => ?Y2:Val)
        Lt |-> (T1:Val => ?T2:Val)
        (list(X1)(B:Seq) list(Y1)(C:Seq) => list(?Y2)(?A:Seq))
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
ensures ?A ==K rev(B) @ C
endmodule
