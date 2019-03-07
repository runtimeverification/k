// Copyright (c) 2018-2019 K Team. All Rights Reserved.

requires "boundary-cells-test.k"

module BOUNDARY-CELLS-TEST-SPEC
  imports BOUNDARY-CELLS-TEST

  rule <k> 0 => 4 </k>
       <c1> 0 => 2 </c1>
       <c2> 0 => 0 </c2>

endmodule
