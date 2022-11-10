// Copyright (c) 2022 K Team. All Rights Reserved.

requires "test.k"

module TEST2-SPEC
    imports TEST

    claim <k> runLemma ( #lookupMemory(( KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY)    ) => doneLemma ( 33  ) ... </k>

endmodule
