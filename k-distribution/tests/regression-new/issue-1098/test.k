
module TEST
  imports DOMAINS

  syntax RecordFieldDescr ::= key:Id "=" value:K
  syntax RecordDescr ::= List{ RecordFieldDescr , ";" }
  syntax Record ::= Map | ".Record"

  syntax RecordDescr ::= "record2descr" "(" Record ")" [function]
  rule record2descr( F:Id |-> V ) => F = V [structural]

  rule 0 => record2descr(x |-> 0)
  syntax Id ::= "x" [token]
endmodule

