// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module EVM-DATA
    imports STRING

    syntax JSON ::= String
 // ----------------------
endmodule

module EVM
    imports EVM-DATA

    configuration
      <kevm>
        <k> $PGM:EthereumCommand </k>
      </kevm>
    syntax EthereumCommand
endmodule

module ETHEREUM-SIMULATION
    imports EVM

    syntax EthereumCommand ::= "load" JSON | "mkTX" Int
 // ---------------------------------------------------
    rule <k> load "transaction" => mkTX !_ID:Int ... </k>
endmodule

module TEST-EXT
    imports ETHEREUM-SIMULATION

    syntax KItem ::= "step"

    rule <k> step => .K ... </k>
endmodule
