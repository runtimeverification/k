module TEST
  imports INT
  imports K-EQUAL

  syntax Int ::= "#ctz" "(" Int ")" [function]
  rule #ctz(N) => #if N modInt 2 ==Int 1 #then 0 #else 1 +Int #ctz(N >>Int 1) #fi  requires N =/=Int 0
endmodule
