This module introduces the basic syntax of arithmetic expressions, with
associativity and precedence encoded explicitly.

```k
module ARITH-SYNTAX
  imports INT-SYNTAX
  syntax Integer  ::= Int
                    | "(" Integer ")" [bracket]
                    > "-" Integer [function]
                    > left: Integer "*" Integer [function]
                    | Integer "/" Integer [function]
                    > left: Integer "+" Integer [function]
                    | Integer "-" Integer [function]
endmodule
```

The evaluation rules for integer arithmetic.

```k
module ARITH
  imports INT
  imports ARITH-SYNTAX

  rule - N => 0 -Int N
  rule N * M => N *Int M
  rule N / M => N /Int M requires M =/=Int 0
  rule N + M => N +Int M
  rule N - M => N -Int M
endmodule
```

Some fragment of k code we wouldn't want to include:
```{.k .exclude}
syntax Nonsense   ::= Wrong()
```

```k
module BOOLS-SYNTAX
  imports BOOL-SYNTAX
  imports ARITH-SYNTAX

  syntax Bool   ::= "(" Bool ")" [bracket]
                  > "!" Bool [function]
                  > left: Bool "&&" Bool [function]
                  > left: Bool "^" Bool [function]
                  > left: Bool "||" Bool [function]
                  > right: Bool "->" Bool [function]

  syntax Bool   ::= Integer "<"  Integer [function]
                  | Integer "<=" Integer [function]
                  | Integer ">"  Integer [function]
                  | Integer ">=" Integer [function]
                  | Integer "==" Integer [function]
                  | Integer "!=" Integer [function]
endmodule

module BOOLS
  imports ARITH
  imports BOOLS-SYNTAX
  imports BOOL

  rule ! B => notBool B
  rule A && B => A andBool B
  rule A ^ B => A xorBool B
  rule A || B => A orBool B
  rule A -> B => A impliesBool B

  rule N < M => N <Int M
  rule N <= M => N <=Int M
  rule N > M => N >Int M
  rule N >= M => N >=Int M
  rule N == M => N ==Int M
  rule N != M => N =/=Int M
endmodule
```
