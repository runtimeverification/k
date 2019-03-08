module NONDET

  import DOMAINS

  syntax S
    ::= "initial"
      | "next1"  | "next2"
      | "final1" | "final2"
      | "unreachable"

  rule initial => next1

  rule initial => next2

  rule next1 => final1

  rule next2 => final2

endmodule
