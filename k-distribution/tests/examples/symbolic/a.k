// Copyright (c) 2016-2019 K Team. All Rights Reserved.

require "domains.k"

module A-SYNTAX

imports INT-SYNTAX
imports BOOL-SYNTAX
imports STRING-SYNTAX

syntax Exp ::= "symInt"
             | "symBool"
             | "symString"
             | Int
             | Bool
             | String
             //
             | symIExp(Int)

syntax Exp ::= if(Exp) [strict]

endmodule

module A

imports INT
imports BOOL
imports STRING

imports A-SYNTAX

configuration <T>
  <k> $PGM:Exp </k>
</T>

syntax KResult ::= Int
                 | Bool
                 | String

rule symInt => ?_:Int
rule symBool => ?_:Bool
rule symString => ?_:String

rule if(0) => 0 [transition]
rule if(1) => 1 [transition]

rule if(true ) => true [transition]
rule if(false) => false [transition]

rule if("t") => "t" [transition]
rule if("f") => "f" [transition]
rule if("") => "default" [transition]

//

rule symIExp(I:Int) => iexp(I)

// uninterpreted function
syntax Int ::= iexp(Int) [function, smtlib(iexp)]

endmodule
