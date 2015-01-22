// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module EXTERNAL

syntax KItem ::= "pp" "(" K ")" [function]
               | "ppsucceed" "(" String ")"
               | "pperror" "(" String ")"

rule S:String => pp(#system("cat\x01" +String S))

rule pp(#systemResult(ExitCode:Int, Stdout:String, Stderr:String)) => ppsucceed(Stdout) when ExitCode ==Int 0
rule pp(#systemResult(ExitCode:Int, Stdout:String, Stderr:String)) => pperror(Stderr) when ExitCode =/=Int 0

endmodule
