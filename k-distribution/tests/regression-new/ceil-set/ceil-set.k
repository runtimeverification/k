// Copyright (c) 2022 K Team. All Rights Reserved.

module CEIL-SET-SYNTAX
    imports SET
    imports INT

    syntax Test ::= testRegular ( Set , Int , Int ) | testGenerated ( Int , Int , Int , Int ) | done ( K )

    syntax Set ::= partialSet ( Set ) [function]
    syntax Int ::= partialInt ( Int ) [function]

endmodule

module CEIL-SET
    imports CEIL-SET-SYNTAX
    imports MAP-SYMBOLIC

    configuration <k> $PGM:Test </k>
                  <genSet>
                    <genElem multiplicity="*" type="Set">
                      <cellA> 0 </cellA>
                      <cellB> 0 </cellB>
                    </genElem>
                  </genSet>

    rule <k> testRegular(SET, I1, I2) => done( partialSet(SET) SetItem(partialInt(I1)) SetItem(partialInt(I2)) ) </k>

    rule <k> testGenerated (I1, I2, I3, I4) => done(.) </k>
         <genSet>
          ( REST => <genElem>
                        <cellA> partialInt(I1) </cellA>
                        <cellB> partialInt(I2) </cellB>
                    </genElem>
                    <genElem>
                        <cellA> partialInt(I3) </cellA>
                        <cellB> partialInt(I4) </cellB>
                    </genElem>
                    REST )
         </genSet>

    rule partialSet(.Set) => .Set
    rule partialInt(0) => 0

endmodule
