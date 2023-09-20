// Copyright (c) K Team. All Rights Reserved.
module TEST-SYNTAX
    imports INT-SYNTAX
endmodule
module MIR-CONFIG
    imports TEST-SYNTAX
    configuration
      <k> $PGM:Int </k>
      <returncode exit=""> 4 </returncode>
endmodule
module TEST
    imports TEST-SYNTAX
    imports MIR-CONFIG
    rule 1 => 2
endmodule
