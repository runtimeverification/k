// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "domains.md"

module VARLABEL-SYNTAX

  syntax Exp ::= Int "+" Int
                 | Int "-" Int

  syntax Holder ::= "holder" "(" Exp ")"

  syntax Finish ::= "finish"
endmodule


module VARLABEL
  imports VARLABEL-SYNTAX


  configuration <T color="yellow">
                  <k color="green"> $PGM:Holder </k>
                </T>
  syntax KItem ::= "main""("Holder")"
  rule Y(X + 1) => main(Y(X + 2))

  rule Z(holder(X + 2)) => finish

endmodule
