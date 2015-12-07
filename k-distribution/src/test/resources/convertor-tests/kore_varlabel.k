require "domains.k"

module VARLABEL-SYNTAX
  imports VARLABEL-COMMON
  imports DOMAINS-SYNTAX
endmodule

module VARLABEL-COMMON
  imports DOMAINS-COMMON

  syntax Exp ::= Int "+" Int
                 | Int "-" Int

  syntax Holder ::= "holder" "(" Exp ")"

  syntax Finish ::= "finish"
endmodule


module VARLABEL
  imports DOMAINS
  imports VARLABEL-COMMON


  configuration <T color="yellow">
                  <k color="green"> $PGM:Holder </k>
                </T>

  rule Y:KLabel(X + 1) => Y(X + 2) 

  rule Z:KLabel(X + 2) => finish

endmodule
