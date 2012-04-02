
module LATEXTEST 
  syntax Exp ::= Exp "[" Exp "]"    [ strict prec(8) latex("{#1}[{#2}]") ]
end module
