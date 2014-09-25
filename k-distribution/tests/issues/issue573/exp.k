// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module EXP-SYNTAX

  // Arithmetics syntax
  syntax Exp ::= #Int
               | Exp "+" Exp [strict] // addition
               | Exp "*" Exp [strict] // multiplication
               | Exp "/" Exp [strict] // division
               | Exp "?" Exp ":" Exp [strict]
               | Exp ";" Exp [seqstrict]
               | "(" Exp ")" [bracket]

  // Input / output syntax
  syntax Exp ::= "read"
               | "print" Exp [strict]

  // Concurrency features
  syntax Exp ::= "spawn" Exp
               | "rendezvous" Exp [strict]

endmodule

module EXP
  imports EXP-SYNTAX
  syntax KResult ::= #Int
  rule I1:#Int + I2:#Int => I1 +Int I2
  configuration
    <k color="green" multiplicity="*"> $PGM:K </k>
    <streams>
      <in color="magenta" stream="stdin"> .List </in>
      <out color="fuchsia" stream="stdout"> .List </out>
    </streams>

  // Arithmetics semantics
  rule I1:#Int + I2:#Int => I1 +Int I2
  rule I1:#Int * I2:#Int => I1 *Int I2
  rule I1:#Int / I2:#Int => I1 /Int I2 when I2 =/=Int 0
  rule 0 ? _ : E:Exp => E
  rule I:#Int ? E:Exp : _ => E when I =/=Int 0
  rule _:#Int ; I2:#Int => I2

  // Input / output semantics
  rule <k> read => I:#Int ... </k>
       <in> ListItem(I) => . ... </in>

  rule <k> print I:#Int => I ... </k>
       <out> ... . => ListItem(I) </out>

  // Concurrency semantics
  rule <k> spawn E => 0 ... </k>
       (. => <k> E </k>)

  rule <k> rendezvous I:#Int => 0 ... </k>
       <k> rendezvous I => 0 ... </k>
endmodule


