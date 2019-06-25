requires "kwasm-lemmas.k"

module SIMPLE-ARITHMETIC-SPEC
    imports WASM
    imports KWASM-LEMMAS

    rule <k> ( ITYPE:IValType . const X:Int ) ( ITYPE . const Y:Int ) => . ... </k>
         <valstack> S:ValStack => < ITYPE > Y : < ITYPE > X : S </valstack>
      requires #inUnsignedRange(ITYPE, X)
       andBool #inUnsignedRange(ITYPE, Y)
endmodule
