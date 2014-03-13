module TEST
  syntax MyMap ::= getModel(Bool) [function, hook(#BOOL:checksat_)]
  syntax Bool ::= "[E]K" K "." Bool
  rule 0 => getModel([E]K X:Int . X:Int >Int 0)
  rule <k> (X |-> _) => .K </k>
  //rule <k> (X |-> I:Int) => . </k> when I >Int 0 // TODO(YilongL): I wanted to write this but it wouldn't kompile
endmodule
