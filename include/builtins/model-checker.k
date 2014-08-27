// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "bool.k"

module LTL-SYNTAX-HOOKS
  imports #LTL-INTERFACE
  syntax #LtlFormula ::= "TrueLtl"
  syntax #LtlFormula ::= "FalseLtl"

  syntax LtlFormula ::= #LtlFormula

endmodule

module LTL-HOOKS
  imports LTL-SYNTAX-HOOKS

  syntax LtlFormula ::= "~Ltl" LtlFormula [function,
                                           latex(\mathop{\sim_{\scriptstyle\it Ltl}}{#1})]
                     |  "OLtl" LtlFormula [function,
                                           latex(\mathop{\mathsf{O}_{\scriptstyle\it Ltl}}{#1})]
                     |  "<>Ltl" LtlFormula [function,
                                            latex(\mathop{\diamond_{\scriptstyle\it Ltl}}{#1})]
                     |  "[]Ltl" LtlFormula [function,
                                            latex(\mathop{\square_{\scriptstyle\it Ltl}}{#1})]
                     | "(" LtlFormula ")" [bracket]
                     >  LtlFormula "/\\Ltl" LtlFormula [function, left,
                                                        latex({#1}\mathrel{\land_{\scriptstyle\it Ltl}}{#2})]
                     >  LtlFormula "\\/Ltl" LtlFormula [function, left,
                                                        latex({#1}\mathrel{\lor_{\scriptstyle\it Ltl}}{#2})]
                     > left:
                        LtlFormula "ULtl" LtlFormula  [function, left,
                                                       latex({#1}\mathrel{\mathsf{U}_{\scriptstyle\it Ltl}}{#2})]
                     |  LtlFormula "RLtl" LtlFormula  [function, left,
                                                       latex({#1}\mathrel{\mathsf{R}_{\scriptstyle\it Ltl}}{#2})]
                     |  LtlFormula "WLtl" LtlFormula  [function, left,
                                                       latex({#1}\mathrel{\mathsf{W}_{\scriptstyle\it Ltl}}{#2})]
                     |  LtlFormula "|->Ltl" LtlFormula [function, left,
                                                        latex({#1}\mathrel{\mapsto_{\scriptstyle\it Ltl}}{#2})]
                     > left:
                        LtlFormula "->Ltl" LtlFormula  [function, left,
                                                        latex({#1}\mathrel{\right{arrow}_{\scriptstyle\it Ltl}}{#2})]
                     |  LtlFormula "<->Ltl" LtlFormula [function, left,
                                                        latex({#1}\mathrel{\leftrightarrow_{\scriptstyle\it Ltl}}{#2})]
                     |  LtlFormula "=>Ltl" LtlFormula  [function, left,
                                                        latex({#1}\mathrel{\Rightarrow_{\scriptstyle\it Ltl}}{#2})]
                     |  LtlFormula "<=>Ltl" LtlFormula [function, left,
                                                        latex({#1}\mathrel{\Leftightarrow_{\scriptstyle\it Ltl}}{#2})]
endmodule

module MODEL-CHECKER-SYNTAX-HOOKS
  imports LTL-SYNTAX-HOOKS
  syntax #ModelCheckerState
  syntax ModelCheckerState ::= #ModelCheckerState
  syntax #Prop
  syntax Prop ::= #Prop
  syntax #ModelCheckResult
  syntax ModelCheckResult ::= #ModelCheckResult
  syntax LtlFormula ::= Prop
endmodule


module  MODEL-CHECKER-INTERFACE
  imports #MODEL-CHECKER-INTERFACE

  syntax Bool ::= Bag "|=Ltl" K [latex({#1}\mathrel{\models_{\scriptstyle\it Ltl}}{#2})]

endmodule

module MODEL-CHECKER-HOOKS
  imports MODEL-CHECKER-INTERFACE
  imports MODEL-CHECKER-SYNTAX-HOOKS
  imports BOOL-HOOKS

  syntax ModelCheckResult ::= "modelCheck" "(" ModelCheckerState "," LtlFormula ")"


endmodule
