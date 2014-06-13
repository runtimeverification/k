// Copyright (c) 2014 K Team. All Rights Reserved.
module TEST

  configuration <T> <k> $PGM:K </k> <bag> <b multiplicity="*"> . </b> </bag> </T>
  
  syntax KItem ::= start(Int)

  syntax Bag ::= mergeBag(Bag, Bag) [function]

  rule mergeBag(B1, B2) => B1 B2
  
  // TODO(YilongL): remove the sort Bag for variable `B'; 
  // right now `B' will be inferred as BagItem without explicit annotation
  rule <k> start(I:Int => I -Int 1) ...</k> <bag> B:Bag => mergeBag(<b> I </b>, B) </bag>
    when I >Int 0
  rule start(0) => .
  
endmodule
