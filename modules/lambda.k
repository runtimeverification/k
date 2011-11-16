require substitution

module LAMBDA imports SUBSTITUTION
  syntax KResult ::= #Id 
                   | "lambda" K       [: prec 100 latex "\lambda{#1}" :]
  syntax K ::= "[" #Id "]"  K         [: latex "{#1}.{#2}" prec 99 gather(e &):]
             | K K                    [:strict prec 0 gather (E e):]

---Function application (through beta-substitution)
  rule <k> (lambda[X:#Id] E:K) V:KResult => E[V / X] ...</k>
end module
