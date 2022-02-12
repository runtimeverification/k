requires "verification.k"

module LOOPING-SPEC
    imports VERIFICATION

    claim <k> while ( 1 <= $n ) {
                $s = $s + $n ;
                $n = $n + -1 ;
              }
           => . ... </k>
          <state> $s |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2))
                  $n |-> (N:Int => 0)
          </state>
      requires N >=Int 0
       andBool S >=Int 0

endmodule

