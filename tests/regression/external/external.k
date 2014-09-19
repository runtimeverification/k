// Copyright (c) 2014 K Team. All Rights Reserved.
module EXTERNAL

syntax KItem ::= "pp" "(" K ")" [function]
               | "ppsucceed" "(" String ")"
               | "pperror" "(" String ")"

rule S:String => pp(#external("cat\x01" +String S))

rule pp(S:String) => ppsucceed(S)
rule pp(#tcpError(S:String)) => pperror(S)

endmodule
