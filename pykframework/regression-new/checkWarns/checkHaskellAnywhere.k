// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CHECKHASKELLANYWHERE-SYNTAX
endmodule

module CHECKHASKELLANYWHERE
  imports CHECKHASKELLANYWHERE-SYNTAX
  imports INT
  rule 1 => 2 [anywhere]
endmodule
