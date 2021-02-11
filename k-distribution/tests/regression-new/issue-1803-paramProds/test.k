module TEST-SYNTAX
  syntax {S1, S2} Exp ::= S1 "+" S2 [klabel(plus), symbol]
  syntax Exp ::= "a" | "b"
  syntax {S} Exp ::= minus(S) [klabel(minus), symbol]
  syntax {S} Exp ::= mul(S) [klabel(mul), symbol]

endmodule

module TEST
  imports TEST-SYNTAX
  imports K-EQUAL-KORE

  rule A + B => #if A ==K a #then B #else b #fi

endmodule
