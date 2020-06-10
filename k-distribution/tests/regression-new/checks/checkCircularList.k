module CHECKCIRCULARLIST-SYNTAX
  imports INT-SYNTAX
  imports LIST

  syntax Exp ::= Int
               | "(" Exp ")" [bracket]
               | Exp "*" Exp [left, strict]
               > Exp "+" Exp [left, strict]
               | Exp "-" Exp [left, strict]

  syntax ExpList ::= List{Exp, ";"} [strict]
  syntax Exp ::= ExpList
               | eval(Exp)  [strict]

  syntax KResult ::= Int | ExpList

endmodule

module CHECKCIRCULARLIST
  imports CHECKCIRCULARLIST-SYNTAX
  imports INT

  rule L::Int + R::Int => L +Int R
  rule L::Int - R::Int => L -Int R
  rule L::Int * R::Int => L *Int R

  rule eval(E::Exp) => E
  rule eval(E::Exp; Es::ExpList) => eval(E); eval(Es)
  rule eval(.ExpList) => .ExpList

  configuration <k> eval($PGM:ExpList) </k>
endmodule

