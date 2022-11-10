module TEST
  imports INT

  configuration
    <k> $PGM:K </k>
    <cells>
      <cell multiplicity="*" type="Map">
        <num> 0 </num>
        <data> 0 </data>
      </cell>
    </cells>

    syntax CellCell ::= #makeCell( Int, Int ) [function]
 // -----------------------------------------------
    rule #makeCell( X, Y ) => (<cell> <num> X </num> <data> Y </data> </cell>)

    syntax KItem ::= "#putCells"
 // ----------------------------
    rule <k> #putCells => . ... </k>
         <cells>
           (.Bag => #makeCell(0, 1))
           (.Bag => <cell> <num> 5 </num> <data> 6 </data> </cell>)
           ...
         </cells>
endmodule
