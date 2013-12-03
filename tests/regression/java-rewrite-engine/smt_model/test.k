module TEST
  syntax MyMap ::= getModel(Bool) [function, hook(#BOOL:checksat_)]
  syntax Bool ::= "[E]K" K "." Bool
  rule 0 => getModel([E]K X:Int . X:Int >Int 0)
endmodule

