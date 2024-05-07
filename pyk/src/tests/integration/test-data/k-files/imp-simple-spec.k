requires "imp-verification.k"

module IMP-FUNCTIONAL-SPEC
    imports IMP-VERIFICATION
    imports K-EQUAL-SYNTAX

    claim [concrete-addition]: 3 +Int 4 => 7

    claim [concrete-addition-fail]: 3 +Int 4 => 0

    claim [concrete-identity]: 0 => 0

    claim [concrete-nonsense]: 0 => 1

    claim [concrete-requires-trivial-false-identity]: 0 => 0
      requires false

    claim [concrete-requires-nontrivial-false-identity]: 0 => 0
      requires 0 ==Int 1

    claim [concrete-requires-trivial-false-nonsense]: 0 => 1
      requires false

    claim [concrete-requires-nontrivial-false-nonsense]: 0 => 1
      requires 0 ==Int 1

    claim [concrete-requires-trivial-false-nonsense-undecided]: _X:Int => ?_Y:Int
      requires false

    claim [concrete-requires-nontrivial-false-nonsense-undecided]: _X:Int => ?_Y:Int
      requires 0 ==Int 1

    claim [symbolic-addition-commutativity]: N +Int M => M +Int N

    claim [ite-sort-param]: (#if false #then 1 #else 2 #fi) => 2

endmodule


module IMP-SIMPLE-SPEC-DEPENDENCIES
    imports IMP-VERIFICATION

    claim [if-almost-same-plus]:
        <k> if (_B:Bool) {$s = $n + $s; } else {$s = $s + $n; } => .K ...</k>
        <state> ($s |-> S:Int $n |-> N:Int) => ($s |-> (S +Int N) $n |-> N) </state>

endmodule

module IMP-SIMPLE-SPEC
    imports IMP-VERIFICATION
    imports IMP-SIMPLE-SPEC-DEPENDENCIES

    claim [addition-1]: <k> 3 + 4 => 7 ... </k>

    claim [addition-2]: <k> $s + $n => 7 ... </k> <state> $s |-> 3 $n |-> 4 </state>

    claim [addition-var]: <k> 3 + N => 7 ... </k> requires N ==Int 4

    claim [pre-branch-proved]: <k> $n = 7 ; if (B:Bool) { $n = 6 ; } else { $n = 5 ; } => if (B:Bool) { $n = 6 ; } else { $n = 5 ; } ... </k>
                               <state> $n |-> (0 => 7) </state>

    claim [while-cut-rule]: <k> while (B:Bool) BB:Block => if (B) { BB while (B) BB } else {} ... </k>

    claim [while-cut-rule-delayed]: <k> $n = 7 ; while (B:Bool) BB:Block => if (B) { BB while (B) BB } else {} ... </k>
                                    <state> $n |-> (_ => ?_) </state>

    claim [bmc-loop-concrete]: <k> while (0 <= $n) { $n = $n + -1 ; }
                                   $i = 1;
                                 => .K ...
                               </k>
                               <state> $n |-> (1 => ?N)
                                       $i |-> (0 => ?I)
                               </state>
      ensures 0 <Int ?N andBool ?I ==Int 1

    claim [bmc-loop-symbolic]: <k> while ($s <= $n) { $n = $n + -1 ; }
                                   $i = 1;
                                => .K ...
                                </k>
                               <state> ($n |-> (1 => ?N)) ($s |-> S)
                                       ($i |-> (0 => ?I))
                               </state>
      requires 0 <=Int S
       ensures 0 <Int ?N andBool ?I ==Int 1

    claim [bmc-two-loops-symbolic]: <k> while ($s <= $n) { $n = $n + -1 ; }
                                        while ($k <= $m) { $m = $m + -1 ; }
                                        $i = 1;
                                     => .K ...
                                    </k>
                                    <state> ($n |-> (1 => ?N)) ($s |-> S)
                                            ($m |-> (1 => ?M)) ($k |-> K)
                                            ($i |-> (0 => ?I))
                                    </state>
      requires 0 <=Int S andBool 0 <=Int K
       ensures 0 <Int ?N andBool 0 <Int ?M andBool ?I ==Int 1

    claim [failing-if]: <k> if(_B:Bool) { $n = 1 ; } else { $n = 2 ; } => .K ... </k>
                        <state> $n |-> (0 => 1) </state>

    claim [sum-10]: <k> int $s, $n, .Ids ; $n = 10 ; while (0 <= $n) { $s = $s + $n ; $n = $n + -1 ; } => .K ... </k>
                    <state> .Map => $s |-> 55 $n |-> -1 </state>

    claim [sum-100]: <k> int $s, $n, .Ids ; $n = 100 ; while (0 <= $n) { $s = $s + $n ; $n = $n + -1 ; } => .K ... </k>
                     <state> .Map => $s |-> 5050 $n |-> -1 </state>

    claim [sum-1000]: <k> int $s, $n, .Ids ; $n = 1000 ; while (0 <= $n) { $s = $s + $n ; $n = $n + -1 ; } => .K ... </k>
                      <state> .Map => $s |-> 500500 $n |-> -1 </state>

    claim [fail-branch]: <k> if ( $s <= 123) { $n = 1; } else { } => .K ... </k>
                         <state> $n |-> (0 => 1) $s |-> _S:Int </state>

    claim [long-branches]: <k> if ( $s <= 123) { 
                                  $n = 0; 
                               } 
                               else { 
                                  $n = 1;
                               } 
                               while($n <= 100) {
                                  $n = $n + 1;
                               }
                               => .K 
                           ...
                           </k>
                         <state> $n |-> (0 => 101) $s |-> _S:Int </state>

    claim [use-if-almost-same]:
        <k> $n = $n + 1; if (_B:Bool) {$s = $n + $s; } else {$s = $s + $n; } $s = $s + 1; => .K ...</k>
        <state> ($s |-> S:Int $n |-> N:Int) => ($s |-> (S +Int N +Int 2) $n |-> N:Int +Int 1) </state>
        [depends(IMP-SIMPLE-SPEC-DEPENDENCIES.if-almost-same-plus)]

    claim [if-almost-same-times]:
        <k> if (_B:Bool) {$s = $n * $s; } else {$s = $s * $n; } => .K ...</k>
        <state> ($s |-> S:Int $n |-> N:Int) => ($s |-> (S *Int N) $n |-> N) </state>

    claim [use-if-almost-same-twice]:
        <k> $n = $n + 1;
            if (_B1:Bool) {$s = $n + $s; } else {$s = $s + $n; }
            if (_B2:Bool) {$s = $n * $s; } else {$s = $s * $n; }
            $s = $s + 1; => .
        ...</k>
        <state> ($s |-> S:Int $n |-> N:Int) => ($s |-> (((S +Int N +Int 1) *Int (N:Int +Int 1)) +Int 1) $n |-> N:Int +Int 1) </state>
        [depends(IMP-SIMPLE-SPEC-DEPENDENCIES.if-almost-same-plus,if-almost-same-times)]

    claim [sum-loop]: <k> while (0 <= $n) { $s = $s + $n ; $n = $n + -1 ; }  => .K ... </k>
                      <state> $s |-> (S => S +Int ((N *Int (N +Int 1)) /Int 2)) $n |-> (N => -1) </state>
                      requires 0 <=Int N
      [circularity]

    claim [sum-N]: <k> int $s, $n, .Ids ; $n = N:Int ; while (0 <= $n) { $s = $s + $n ; $n = $n + -1 ; } => .K ... </k>
                      <state> .Map => $s |-> ((N *Int (N +Int 1)) /Int 2) $n |-> -1 </state>
                    requires 0 <=Int N
                    [depends(sum-loop)]


    claim [failing-circularity]: <k> $n = $n + 1; => .K ... </k>
                                 <state> $n |-> N => $n |-> N </state>
                                 requires 0 <=Int N
                                 [circularity]

    claim [fail-early]: <k> if ($n <= 1) {
                              $s = 1;
                            }
                            else {
                              while ($k <= 9) {
                                $k = ($k + 1);
                              }
                              $s = 1;
                            } => .
                            ...
                        </k>
                        <state>
                          $s |-> (0 => 2)
                          $n |-> N:Int
                          $k |-> (0 => 10)
                        </state>
                      requires 0 <=Int N

    claim [simple-untrue]:
      <state>... $s |-> (1 => 2) ...</state>

    claim [dep-fail-1]:
      <k> $s = $s + 1; => .K ...</k>
      <state> $s |-> (0 => 2) </state>
      [depends(simple-untrue)]

    claim [terminal-node-subsumption]: 
      <k> $n = $n + 1; => .K </k>
      <state> $n |-> ( N => N +Int 1 ) </state>
      requires 0 <=Int N  

endmodule
