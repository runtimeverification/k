module ISSUE
  configuration <k> a </k> <out stream="stdout"> .List </out>
  syntax K ::= "a"
  rule a => (SetItem(1) in SetItem(1))
  rule <k> true => .K ...</k> <out>... .List => ListItem("success") </out>
  rule <k> false => .K ...</k> <out>... .List => ListItem("fail") </out>
endmodule
