module LESSON-18-A-SYNTAX
endmodule

module LESSON-18-A
  imports LESSON-18-A-SYNTAX

  imports INT
  imports BOOL
  imports K-EQUAL

  syntax Exp  ::= Int | Bool
                | "if" "(" Exp ")" Exp "else" Exp [strict(1)]

  syntax Int  ::= termsEqual(K, K) [function]

  syntax Bool ::= isKResult(K) [function, symbol]
  rule isKResult(_:Int) => true
  rule isKResult(_:Bool) => true

  rule if (B:Bool) E1:Exp else E2:Exp => #if B #then E1 #else E2 #fi

  rule termsEqual(K1, K2) => #if K1 ==K K2 #then 0 #else 1 #fi
endmodule
