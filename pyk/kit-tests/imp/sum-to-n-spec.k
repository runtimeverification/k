// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module SUM-TO-N-SPEC
  imports IMP-VERIFICATION
  claim [main]:
        <k> int $n, $s;
            $n = N:Int;
            $s = 0;
            while (!($n <= 0)) {
              $s = $s + $n;
              $n = $n + -1;
            }
         => .K
        </k>
        <state> .Map => ?_ </state>
    requires N >=Int 0
endmodule
