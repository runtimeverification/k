// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST-SYNTAX
    imports INT-SYNTAX
endmodule
module MIR-CONFIG
    imports TEST-SYNTAX
    configuration
      <k> $PGM:Int </k>
      <b> 4 </b>
endmodule
module TEST
    imports TEST-SYNTAX
    imports MIR-CONFIG
    rule 1 => 2
endmodule
