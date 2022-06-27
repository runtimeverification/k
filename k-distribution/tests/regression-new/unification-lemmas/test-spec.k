// Copyright (c) 2022 K Team. All Rights Reserved.

requires "test.k"

module TEST-SPEC
    imports TEST

  claim <k> makeLookup(B) => 1 ... </k>
    requires lookup(#hashedLocation(B .IntList)) ==Int 1
     andBool #rangeUInt(B)

endmodule
