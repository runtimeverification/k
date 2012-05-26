require "builtins/bool.k"

module LTL-SYNTAX-HOOKS
  syntax LTLFormula ::= #LTLFormula 
endmodule

module LTL-HOOKS
  imports LTL-SYNTAX-HOOKS

//  syntax LTLFormula ::= "LTLTrue" [hook(#LTL:LTLTrue)]

//  syntax LTLFormula ::= "LTLFalse" [hook(#LTL:LTLFalse)]

  syntax LTL ::= "justforK2"

  syntax LTLFormula ::= "LTL~" LTLFormula  [function, prec(53), hook(#LTL:LTL~_)]


  syntax LTLFormula ::= LTLFormula "LTL/\\" LTLFormula 
      [function, prec(55), gather(E e),  hook(#LTL:_LTL&&_)]

  syntax LTLFormula ::= LTLFormula "LTL\\/" LTLFormula 
      [function, prec(59), gather(E e), hook(#LTL:_LTL||_)]

  syntax LTLFormula ::= "LTLO" LTLFormula 
      [function, prec(53), hook(#LTL:LTLO_)]

  syntax LTLFormula ::= LTLFormula "LTLU" LTLFormula 
      [function, prec(63), hook(#LTL:_LTLU_)]

  syntax LTLFormula ::= LTLFormula "LTLR" LTLFormula 
      [function, prec(63), hook(#LTL:_LTLR_)]

  syntax LTLFormula ::= LTLFormula "LTL->" LTLFormula 
      [function, prec(65), gather(e E), hook(#LTL:_LTL->_)]

  syntax LTLFormula ::= LTLFormula "LTL<->" LTLFormula 
      [function, prec(65), hook(#LTL:_LTL<->_)]

  syntax LTLFormula ::= "LTL<>" LTLFormula 
      [function, prec(53), hook(#LTL:LTL<>_)]

  syntax LTLFormula ::= "LTL[]" LTLFormula 
      [function, prec(53), hook(#LTL:LTL@_)]
 
  syntax LTLFormula ::= LTLFormula "LTLW" LTLFormula 
      [function, prec(63), hook(#LTL:_LTLW_)]

  syntax LTLFormula ::= LTLFormula "LTL|->" LTLFormula   // leads-to
      [function, prec(63), hook(#LTL:_LTL|->_)]

  syntax LTLFormula ::= LTLFormula "LTL=>" LTLFormula 
      [function, prec(65), gather (e E), hook(#LTL:_LTL=>_)]

  syntax LTLFormula ::= LTLFormula "LTL<=>" LTLFormula 
      [function, prec(65), hook(#LTL:_LTL<=>_)]

endmodule

module MODEL-CHECKER-SYNTAX-HOOKS
  syntax ModelCheckerState ::= #ModelCheckerState 
  syntax Prop ::= #Prop
  syntax ModelCheckResult ::= #ModelCheckResult
endmodule

module MODEL-CHECKER-HOOKS
  imports MODEL-CHECKER-SYNTAX-HOOKS
  imports LTL-SYNTAX-HOOKS
  imports BOOL-HOOKS


  syntax Bool ::= ModelCheckerState "LTL|=" Prop
      [function, hook(#MODEL-CHECKER:_LTL|=_)]

  syntax ModelCheckResult ::= "modelCheck" "(" ModelCheckerState "," LTLFormula ")" 
         [function, hook(#MODEL-CHECKER:modelCheck)]

endmodule
