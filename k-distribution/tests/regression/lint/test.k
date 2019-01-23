// Copyright (c) 2013-2019 K Team. All Rights Reserved.

// Testing to see if /include directory has any warnings.
// This file should be kompiled with the --warnings-to-errors option and -w all
module TEST-SYNTAX

endmodule

module TEST
  imports TEST-SYNTAX

endmodule
