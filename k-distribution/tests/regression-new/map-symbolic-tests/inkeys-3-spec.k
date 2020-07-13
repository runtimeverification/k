// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module INKEYS-3-SPEC
    imports MAP-TESTS

    rule <k> inkeys ( Y:MyId in_keys ( M:Map ) ) =>   inkeysResult ( Y in_keys ( M ) )  </k> requires notBool Y in_keys(M)

endmodule
