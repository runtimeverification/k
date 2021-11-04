require "test.k"

module TEST-SPEC
    imports TEST
                     
    claim <k> runLemma(3 ^Int X <=Int 3 ^Int Y) => doneLemma(true) ... </k>
      requires 0 <Int X andBool 0 <Int Y
       andBool X <=Int Y
endmodule
