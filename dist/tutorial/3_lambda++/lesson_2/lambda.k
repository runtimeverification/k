module LAMBDA
  syntax Exp ::= Id
               | "lambda" Id "." Exp  [latex(\lambda{#1}.{#2})]
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]

  configuration <T>
                  <k> $PGM:Exp </k>
                  <env> .Map </env>
                  <store> .Map </store>
                </T>

  syntax Val ::= closure(Map,Id,Exp)
  syntax Exp ::= Val
  syntax KResult ::= Val

  rule <k> lambda X:Id . E => closure(Rho,X,E) ...</k> <env> Rho </env>
    [structural]
  rule <k> closure(Rho,X,E) V:Val => E ~> env(Rho') ...</k>
       <env> Rho' => Rho[N/X] </env>
       <store>... . => (N |-> V) ...</store>
    when fresh(N:Nat)
  rule <k> X => V ...</k> <env>...X|->N...</env> <store>...N|->V...</store>

// Auxiliary task
  syntax K ::= env(Map)
  rule <k> _:Val ~> (env(Rho) => .) ...</k> <env> _ => Rho </env>
    [structural]
endmodule
