requires "test.k"


module A3-SPEC
  import TEST

  rule [unif-map]: { MAP [ K <- V ] #Equals MAP:Map [ K <- V' ] } => { V #Equals V' } [simplification, anywhere]

  claim <k> a => b </k> <mem> MEM => MEM [ 3 <- ?C ] </mem>
       ensures ?C <=Int 5 andBool 5 <=Int ?C
endmodule
