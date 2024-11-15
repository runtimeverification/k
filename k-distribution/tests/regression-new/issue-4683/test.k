module TEST
  imports BOOL

  syntax KResult

  syntax Stuff ::= "a" | "b" | "c"
  syntax KItem ::= thing(Stuff, Stuff)  [seqstrict, result(MyResult)]

  rule thing(c, c) => .K

  rule b => c
  rule a => c

  syntax Bool ::= isMyResult(K)  [function, total, symbol(isMyResult)]
  rule isMyResult(_) => false  [owise]
  rule isMyResult(c) => true


endmodule
