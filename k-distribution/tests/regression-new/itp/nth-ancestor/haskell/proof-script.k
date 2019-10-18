// K ITP proof script language

module PROOF-SCRIPT

    imports STRING
    imports MAP

    configuration <T>
      <k> $PGM:Script </k>
      <g> .K </g> // workspace
      <p> .Map </p> // premises
    </T>

    syntax Pred ::= Pred "and" Pred
                  | "none"
                  | Bool

    syntax Script ::= apply(String)
                    | load(String)
                    | store1(String)
                    | store2(String, String)

    rule [load]:
    <k> load(N) => . ... </k>
    <g> X => #if X ==K none
             #then         M [ N ]
             #else X and { M [ N ] }:>Pred
             #fi </g>
    <p> M </p>

    rule [store1]:
    <k> store1(N) => . ... </k>
    <g> X => none </g>
    <p> M => M [ N <- X ] </p>

    rule [store2]:
    <k> store2(N1,N2) => . ... </k>
    <g> X1 and X2 => none </g>
    <p> M => M [ N1 <- X1 ]
               [ N2 <- X2 ] </p>

endmodule
