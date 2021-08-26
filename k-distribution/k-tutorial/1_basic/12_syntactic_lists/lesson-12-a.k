module LESSON-12-A-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX

  syntax Ints     ::= List{Int, ","}

  syntax Strings  ::= List{String, "/"}
endmodule

module LESSON-12-A
  imports LESSON-12-A-SYNTAX
  imports INT
  imports STRING

  syntax Int    ::= sum(Ints) [function]

  rule sum(I:Int, Is:Ints) => I +Int sum(Is)
  rule sum(_) => 0 [owise]

  syntax String ::= concats(Strings) [function]

  rule concats(S:String / Ss:Strings) => S +String concats(Ss)
  rule concats(_) => "" [owise]
endmodule
