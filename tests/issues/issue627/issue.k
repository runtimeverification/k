module ISSUE

syntax NAME ::= Id
syntax Exp ::= NAME [atom]
                      | tuple(Exp) [atom, klabel('Tuple)]
                      | Exp "." NAME [primary]

syntax priorities atom > primary

syntax #Id ::= "x"
rule 5 => isExp(x)

endmodule
