// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
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

    syntax CellCellMap ::= #makeCell( Int, Int ) [function]
 // ----------------------------
    rule #makeCell( X, Y ) => CellCellMapItem(
      <num> X </num>,
      <cell> <num> X </num> <data> Y </data> </cell>
    )

    syntax KItem ::= "#putCells"
 // ----------------------------
    rule <k> #putCells => #makeCell(0,0) (#makeCell(1,1) .CellCellMap) </k>
endmodule
