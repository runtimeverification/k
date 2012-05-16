
module BASIC-RUN 
  configuration <T> <k> .K </k> </T>
  
  //op run : KLabel -> Bag
  syntax Bag ::= "run" KLabel
  
  // This was a macro
  rule run(KL:KLabel) = <T>... <k>KL(.List{K})</k> ...</T>
endmodule
