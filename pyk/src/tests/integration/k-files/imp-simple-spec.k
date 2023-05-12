requires "imp-verification.k"

module IMP-FUNCTIONAL-SPEC
    imports IMP-VERIFICATION

    claim [concrete-addition]: 3 +Int 4 => 7

    claim [concrete-addition-fail]: 3 +Int 4 => 0

   claim [concrete-identity]: 0 => 0

   claim [concrete-nonsense]: 0 => 1

   claim [concrete-requires-trivial-false-identity]: 0 => 0
     requires False

   claim [concrete-requires-nontrivial-false-identity]: 0 => 0
     requires 0 ==Int 1

//   TODO: this should be trivially passing but it fails because cterm_implies returns None
//   claim [concrete-requires-trivial-false-nonsense]: 0 => 1
//     requires False

   claim [concrete-requires-nontrivial-false-nonsense]: 0 => 1
     requires 0 ==Int 1

   claim [concrete-requires-trivial-false-nonsense-undecided]: _X:Int => ?_Y:Int
     requires False

   claim [concrete-requires-nontrivial-false-nonsense-undecided]: _X:Int => ?_Y:Int
      requires 0 ==Int 1

    claim [symbolic-addition-commutativity]: N +Int M => M +Int N

endmodule

module IMP-SIMPLE-SPEC
    imports IMP-VERIFICATION

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
                                 => . ...
                               </k>
                               <state> $n |-> (1 => ?N)
                                       $i |-> (0 => ?I)
                               </state>
      ensures 0 <Int ?N andBool ?I ==Int 1

    claim [bmc-loop-symbolic]: <k> while ($s <= $n) { $n = $n + -1 ; }
                                   $i = 1;
                                => . ...
                                </k>
                               <state> ($n |-> (1 => ?N)) ($s |-> S)
                                       ($i |-> (0 => ?I))
                               </state>
      requires 0 <=Int S
       ensures 0 <Int ?N andBool ?I ==Int 1

    claim [bmc-two-loops-symbolic]: <k> while ($s <= $n) { $n = $n + -1 ; }
                                        while ($k <= $m) { $m = $m + -1 ; }
                                        $i = 1;
                                     => . ...
                                    </k>
                                    <state> ($n |-> (1 => ?N)) ($s |-> S)
                                            ($m |-> (1 => ?M)) ($k |-> K)
                                            ($i |-> (0 => ?I))
                                    </state>
      requires 0 <=Int S andBool 0 <=Int K
       ensures 0 <Int ?N andBool 0 <Int ?M andBool ?I ==Int 1

    claim [failing-if]: <k> if(_:Bool) { $n = 1 ; } else { $n = 2 ; } => . ... </k>
                        <state> $n |-> (0 => 1) </state>

    claim [sum-10]: <k> int $s, $n, .Ids ; $n = 10 ; while (0 <= $n) { $s = $s + $n ; $n = $n + -1 ; } => . ... </k>
                    <state> .Map => $s |-> 55 $n |-> -1 </state>

    claim [sum-100]: <k> int $s, $n, .Ids ; $n = 100 ; while (0 <= $n) { $s = $s + $n ; $n = $n + -1 ; } => . ... </k>
                     <state> .Map => $s |-> 5050 $n |-> -1 </state>

    claim [sum-1000]: <k> int $s, $n, .Ids ; $n = 1000 ; while (0 <= $n) { $s = $s + $n ; $n = $n + -1 ; } => . ... </k>
                      <state> .Map => $s |-> 500500 $n |-> -1 </state>

    claim [fail-branch]: <k> if ( $s <= 123) { $n = 1; } else { } => . ... </k>
                         <state> $n |-> (0 => 1) $s |-> _S:Int </state>
    
    claim [if-almost-same]:
        <k> if (_B:Bool) {$s = $n + $s; } else {$s = $s + $n; } => . ...</k>
        <state> ($s |-> S:Int $n |-> N:Int) => ($s |-> (S +Int N) $n |-> N) </state>
    
    // The vision is that the proof of `use-if-almost-same` will re-use the proof of `if-almost-same`
    // and then it will be without branching.
    claim [use-if-almost-same]:
        <k> $n = $n + 1; if (_B:Bool) {$s = $n + $s; } else {$s = $s + $n; } $s = $s + 1; => . ...</k>
        <state> ($s |-> S:Int $n |-> N:Int) => ($s |-> (S +Int N +Int 2) $n |-> N:Int +Int 1) </state>

endmodule
