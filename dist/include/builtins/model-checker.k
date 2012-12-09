require "bool.k"

module LTL-SYNTAX-HOOKS
  imports #LTL-INTERFACE
  syntax #LtlFormula ::= "TrueLtl"
  syntax #LtlFormula ::= "FalseLtl"

  syntax LtlFormula ::= #LtlFormula

  syntax LTLFormula ::= LtlFormula      // just for compatibility

endmodule

module LTL-HOOKS
  imports LTL-SYNTAX-HOOKS


  syntax LtlFormula ::= "(" LtlFormula ")" [bracket]

  syntax LtlFormula ::= "~Ltl" LtlFormula [function,
                                           latex(\mathop{\sim_{\scriptstyle\it Ltl}}{#1})]
//                                           hook(#LTL:~Ltl_)]
                     |  "OLtl" LtlFormula [function,
                                           latex(\mathop{\mathsf{O}_{\scriptstyle\it Ltl}}{#1})]
//                                           hook(#LTL:OLtl_)]
                     |  "<>Ltl" LtlFormula [function,
                                            latex(\mathop{\diamond_{\scriptstyle\it Ltl}}{#1})]
//                                            hook(#LTL:<>Ltl_)]
                     |  "[]Ltl" LtlFormula [function,
                                            latex(\mathop{\square_{\scriptstyle\it Ltl}}{#1})]
//                                            hook(#LTL:@Ltl_)]
                     >  LtlFormula "/\\Ltl" LtlFormula [function, left,
                                                        latex({#1}\mathrel{\land_{\scriptstyle\it Ltl}}{#2})]
//                                                        hook(#LTL:_&&Ltl_)]
                     >  LtlFormula "\\/Ltl" LtlFormula [function, left,
                                                        latex({#1}\mathrel{\lor_{\scriptstyle\it Ltl}}{#2})]
//                                                        hook(#LTL:_||Ltl_)]
                     > left:
                        LtlFormula "ULtl" LtlFormula  [function, left,
                                                       latex({#1}\mathrel{\mathsf{U}_{\scriptstyle\it Ltl}}{#2})]
//                                                       hook(#LTL:_ULtl_)]
                     |  LtlFormula "RLtl" LtlFormula  [function, left,
                                                       latex({#1}\mathrel{\mathsf{R}_{\scriptstyle\it Ltl}}{#2})]
//                                                       hook(#LTL:_RLtl_)]
                     |  LtlFormula "WLtl" LtlFormula  [function, left, 
                                                       latex({#1}\mathrel{\mathsf{W}_{\scriptstyle\it Ltl}}{#2})]
//                                                       hook(#LTL:_WLtl_)]
                     |  LtlFormula "|->Ltl" LtlFormula [function, left,
                                                        latex({#1}\mathrel{\mapsto_{\scriptstyle\it Ltl}}{#2})]
//                                                        hook(#LTL:_|->Ltl_)]
                     > left:
                        LtlFormula "->Ltl" LtlFormula  [function, left,
                                                        latex({#1}\mathrel{\right{arrow}_{\scriptstyle\it Ltl}}{#2}),
                                                        hook(#LTL:_->Ltl_)]
                     |  LtlFormula "<->Ltl" LtlFormula [function, left,
                                                        latex({#1}\mathrel{\leftrightarrow_{\scriptstyle\it Ltl}}{#2}),
                                                        hook(#LTL:_<->Ltl_)]
                     |  LtlFormula "=>Ltl" LtlFormula  [function, left,
                                                        latex({#1}\mathrel{\Rightarrow_{\scriptstyle\it Ltl}}{#2})]
//                                                        left, hook(#LTL:_=>Ltl_)]
                     |  LtlFormula "<=>Ltl" LtlFormula [function, left,
                                                        latex({#1}\mathrel{\Leftightarrow_{\scriptstyle\it Ltl}}{#2})]
//                                                        hook(#LTL:_<=>Ltl_)]
endmodule

module MODEL-CHECKER-SYNTAX-HOOKS
  imports LTL-SYNTAX-HOOKS
  syntax ModelCheckerState ::= #ModelCheckerState 
  syntax Prop ::= #Prop
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
       //  [function, hook(#MODEL-CHECKER:modelCheck)]


endmodule
