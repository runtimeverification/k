// Copyright (c) 2014-2019 K Team. All Rights Reserved.
require "domains.k"

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
