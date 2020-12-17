module INVALIDAS
  imports DOMAINS

  rule (0 #as 0) => 0 // Found #as pattern where the right side is not a variable.
  rule Y => (0 #as Y) // #as is not allowed in the RHS of a rule. - issue #753
  rule (0 => 1) #as X // Rewrites are not allowed inside an #as pattern.

endmodule
