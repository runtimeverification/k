requires "imp-verification.k"

module IMP-SIMPLE-SPEC
    imports IMP-VERIFICATION

    claim [addition-1]: <k> 3 + 4 => 7 ... </k>

    claim [addition-2]: <k> $s + $n => 7 ... </k> <state> $s |-> 3 $n |-> 4 </state>

    claim [addition-var]: <k> 3 + N => 7 ... </k> requires N ==Int 4

    claim [sum-10]: <k> int $s, $n, .Ids ; $n = 10 ; while (0 <= $n) { $s = $s + $n ; $n = $n + -1 ; } ~> #FINISH => . ... </k>
                     <state> .Map => $s |-> 55 $n |-> -1 </state>

    claim [sum-100]: <k> int $s, $n, .Ids ; $n = 100 ; while (0 <= $n) { $s = $s + $n ; $n = $n + -1 ; } ~> #FINISH => . ... </k>
                     <state> .Map => $s |-> 5050 $n |-> -1 </state>

    claim [sum-1000]: <k> int $s, $n, .Ids ; $n = 1000 ; while (0 <= $n) { $s = $s + $n ; $n = $n + -1 ; } ~> #FINISH => . ... </k>
                      <state> .Map => $s |-> 500500 $n |-> -1 </state>
endmodule
