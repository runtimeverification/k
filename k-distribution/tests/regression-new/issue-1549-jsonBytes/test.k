module TEST-SYNTAX
  imports STRING-SYNTAX
endmodule

module TEST
    imports TEST-SYNTAX
    imports BYTES
    
    configuration <k> String2Bytes($PGM:String) </k>
endmodule
