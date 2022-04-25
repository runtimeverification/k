module TEST
  imports DOMAINS
  imports K-IO

  syntax Foo ::= foo(Int)
               | frob(String, Bool)

  syntax Bar ::= "bar" Foo "*" Foo [format(%1%i%n%2 %3 %4)]
               | "(" Bar ")" [bracket]

  rule bar F1 * F2 =>
    #let _ = #trace(F1) #in
    (#trace(F2) ~> #trace(bar foo(2) * foo(0)) ~> .K)
endmodule
