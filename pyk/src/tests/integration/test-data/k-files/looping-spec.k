requires "imp-verification.k"

module LOOPING-SPEC
    imports IMP-VERIFICATION

    rule [if-true-true]: <k> if (true && true)  S else _ => S ... </k> [priority(80)]

    claim <k> while ( 1 <= $n ) {
                $s = $s + $n ;
                $n = $n + -1 ;
              }
           => .K ... </k>
          <state> $s |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2))
                  $n |-> (N:Int => 0)
          </state>
      requires N >=Int 0
       andBool S >=Int 0

endmodule

