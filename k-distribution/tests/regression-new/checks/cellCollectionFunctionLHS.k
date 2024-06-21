module CELLCOLLECTIONFUNCTIONLHS
  imports BOOL
  imports INT
  imports MAP

  configuration <k> $PGM:K </k>
                <cells>
                  <cell multiplicity="*" type="Map">
                    <addr> 0 </addr>
                    <baz> 0 </baz>
                  </cell>
                </cells>


  syntax KItem ::= "foo"
  rule <k> foo => X </k> <cell> <addr> bar() </addr> <baz> X:Int </baz> </cell>
  rule <k> foo => 0 </k> <cell> <addr> 0 </addr> <baz> bar() </baz> </cell>

  syntax Int ::= bar() [function]
  rule bar() => 0
endmodule
