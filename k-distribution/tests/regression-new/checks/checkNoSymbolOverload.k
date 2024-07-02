module CHECKNOSYMBOLOVERLOAD-SYNTAX
endmodule

module CHECKNOSYMBOLOVERLOAD
  syntax LVal
  syntax RVal
  syntax Val ::= LVal | RVal
  syntax Exp ::= Val

  syntax RVals ::= RVal [overload(arg)]
  syntax Vals  ::= Val  [overload(arg), symbol(val)]
  syntax Exps  ::= Exp  [overload(arg)]
endmodule
