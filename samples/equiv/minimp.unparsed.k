// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "bool.k"
require "k-prelude.k"
require "k-equal.k"
require "int.k"
require "bool.k"
require "int.k"
require "int.k"
require "float.k"
require "string.k"
require "builtins/string.k"
require "builtins/k-equal.k"
require "int.k"
require "int.k"
require "bool.k"
require "int.k"
require "array.k"
require "float.k"
require "string.k"
require "id.k"
require "io/tcp.k"
require "k-equal.k"
require "random.k"
require "counter.k"
require "builtins/builtins.k"
require "builtins/k-equal.k"
require "pattern-matching.k"
require "builtins/symbolic-k.k"
require "k-prelude.k"
require "builtins.k"
require "modules/substitution.k"
require "builtins/builtins.k"
require "k-prelude.k"
require "builtins/symbolic-k.k"
require "io/uris.k"
module MINIMP-SYNTAX

    imports AUTO-INCLUDED-MODULE
    syntax Exp ::= Id
                 | Int
                 | Bool
                 | Exp "i+" Exp [strict, klabel('_i+_)]
                 | Exp "i-" Exp [strict, klabel('_i-_)]
                 | Exp "i==" Exp [strict, klabel('_i==_)]
                 | Exp "i<" Exp [strict, klabel('_i<_)]

    syntax Stmt ::= Id ":=" Exp [strict(2), klabel('_:=_)]
                  | "skip" [klabel('skip)]
                  | Stmt ";" Stmt [left, klabel('_;_)]
                  | "if" Exp "then" Stmt "else" Stmt [strict(1), klabel
                  ('if_then_else_)]
                  | "while" Exp "do" Stmt [klabel('while_do_)]
                  | "{" Stmt "}" [bracket, klabel('{_})]

    syntax Code ::= Exp
                  | Stmt

endmodule

module MINIMP

    imports AUTO-INCLUDED-MODULE
    imports MINIMP-SYNTAX
    configuration
        <t>
            <k>
                $PGM:K
            </k>
            <env>
                .Map
            </env>
        </t>

    syntax KResult ::= Int
                     | Bool

    rule <k> I:Id => I1:Int ...</k> <env>... I |-> I1 ...</env>

    rule I1:Int i+ I2:Int => I1 +Int I2

    rule I1:Int i- I2:Int => I1 -Int I2

    rule I1:Int i== I2:Int => I1 ==Int I2

    rule I1:Int i< I2:Int => I1 <Int I2

    rule <k> I:Id := I1:Int => .K ...</k> <env>... I |-> ((_:K => I1)) ...
      </env>

    rule <k> I:Id := I1:Int => .K ...</k> <env> Rho:Map ((.Map => I |-> I1))
      </env> when notBool (I in (keys (Rho)))

    rule S1:Stmt ; S2:Stmt => S1 ~> S2

    rule if #token("#Bool", "true")(.KList) then S1:Stmt else _:K => S1

    rule if #token("#Bool", "false")(.KList) then _:K else S2:Stmt => S2

    rule while E:Exp do S:Stmt => if E then (S ; (while E do S)) else skip

endmodule

