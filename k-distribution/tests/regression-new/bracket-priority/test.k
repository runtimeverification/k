module TEST
  imports ID
  imports INT

syntax Exp ::= "(" Name ExpList ")"
syntax Exp ::= Int
             | Name
syntax Name ::= Id
syntax ExpList ::= List{Exp,""} [expList]
syntax Name ::= BuiltinName
syntax BuiltinName ::= "+"

rule (+ I1:Int I2:Int) => I1 +Int I2

syntax priorities defaultBracket > expList

endmodule
