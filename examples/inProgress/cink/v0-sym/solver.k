require sym-int
require ../../../../k-prelude

kmod SOLVER is including SYM-INT + K + K-CONDITION-SEARCH

  syntax K ::= ExpBool
  
  rule (EB1:ExpBool orBool EB2:ExpBool) => EB1
  rule (EB1:ExpBool orBool EB2:ExpBool) => EB2
  rule ExpBool2Int(EB:ExpBool) => 0 if search(EB => false)  
  rule ExpBool2Int(EB:ExpBool) => 1 if search(EB => true)   
  rule EB andBool EB => EB  [structural]

/*
  s@t = satisfiable but not tautology
  uns@t = unsatisfiable
*/
  syntax ExpBool ::= s@t | uns@t | s@lve ExpBool

  rule s@lve true => s@t [structural]
  rule s@lve (SI:SymInt ==Int I:Int) => s@t [structural]
  rule s@lve (SI <=Int I) => s@t [structural]
  rule s@lve (SI >=Int I) => s@t [structural]
  rule s@lve (SI <Int I) => s@t  [structural]
  rule s@lve (SI >Int I) => s@t [structural]
  rule s@lve (SI !=Int I) => s@t [structural]

  rule s@lve false => uns@t [structural]
  rule s@lve (SI <Int SI) => uns@t [structural]
  rule s@lve (SI >Int SI) => uns@t [structural]
  rule s@lve (SI !=Int SI) => uns@t [structural]
  rule s@lve (SI !=Int I andBool SI ==Int I) => uns@t [structural]
  rule s@lve (SI <Int SI':SymInt andBool SI' <Int SI) => uns@t [structural]
  rule s@lve (SI >Int SI':SymInt andBool SI' >Int SI) => uns@t [structural] 
  

  rule s@lve (EB andBool uns@t) => uns@t [structural]
  rule s@lve (EB orBool s@t) => s@t [structural]

endkm
