// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CHECKRESERVEDCELLNAMES-SYNTAX
  imports INT-SYNTAX

endmodule

module CHECKRESERVEDCELLNAMES
     imports INT
     imports CHECKRESERVEDCELLNAMES-SYNTAX

  configuration
    <k> $PGM </k>
    <generatedCounter> 0 </generatedCounter>
    <generatedTop> 1 </generatedTop>

endmodule
