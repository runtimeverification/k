module TEST
  imports DOMAINS

  syntax Pgm ::= "addCell"
               | "foo"
               | "bar"
               | "buzz"
               | Pgm Pgm [right]

  configuration <cells>
                  <cell multiplicity="*" type="Map">
                    <id> 0 </id>
                    <k> $PGM:Pgm </k>
                  </cell>
                </cells>
                <order> .K </order>

  rule <k> addCell => .  ... </k>
       <id> Id </id>
       (.Bag => <cell>
                  <id> Id +Int 1 </id>
                  <k> foo </k> ...
                </cell> )

  rule P1:Pgm P2:Pgm => P1 ~> P2

  rule <k> foo => buzz ... </k>
       <order> . => ListItem(foo) ... </order>

  rule <k> bar => buzz ... </k>
       <order> . => ListItem(bar) ... </order> [priority(250)]

endmodule
