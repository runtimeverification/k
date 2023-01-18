// Copyright (c) K Team. All Rights Reserved.
module TEST-SYNTAX
  imports FLOAT-SYNTAX
  imports ID
endmodule

module TEST
 imports TEST-SYNTAX
 configuration <k> $PGM:Float </k>
endmodule
