// Copyright (c) 2022 K Team. All Rights Reserved.

module CEIL-SET-SYNTAX
    imports SET
    imports INT

    syntax Test ::= testRegular ( Set , Int , Int ) | testCell ( Int , Int , Int , Int ) | done ( K )

    syntax Set ::= partialSet ( Set ) [function]
    syntax Int ::= partialInt ( Int ) [function]

endmodule

module CEIL-SET
    imports CEIL-SET-SYNTAX

    configuration <k> $PGM:Test </k>
                  <cellSet>
                    <cellElem multiplicity="*" type="Set">
                      <cellA> 0 </cellA>
                      <cellB> 0 </cellB>
                    </cellElem>
                  </cellSet>

    rule <k> testRegular(SET, I1, I2) => done( partialSet(SET) SetItem(partialInt(I1)) SetItem(partialInt(I2)) ) </k>

    rule <k> testCell (I1, I2, I3, I4) => done(.) </k>
         <cellSet>
          ( REST => <cellElem>
                        <cellA> partialInt(I1) </cellA>
                        <cellB> partialInt(I2) </cellB>
                    </cellElem>
                    <cellElem>
                        <cellA> partialInt(I3) </cellA>
                        <cellB> partialInt(I4) </cellB>
                    </cellElem>
                    REST )
         </cellSet>

    rule partialSet(.Set) => .Set
    rule partialInt(0) => 0

endmodule
