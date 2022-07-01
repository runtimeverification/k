// Copyright (c) 2022 K Team. All Rights Reserved.

module CEIL-MAP-SYNTAX
    imports MAP
    imports INT

    syntax Test ::= testRegular ( Map , Int , Int , Int , Int ) | testCell ( Int , Int , Int , Int , Int , Int ) | done ( K )

    syntax Map ::= partialMap ( Map ) [function]
    syntax Int ::= partialInt ( Int ) [function]

endmodule

module CEIL-MAP
    imports CEIL-MAP-SYNTAX

    configuration <k> $PGM:Test </k>
                  <cellMap>
                    <cellElem multiplicity="*" type="Map">
                      <key>   0 </key>
                      <cellA> 0 </cellA>
                      <cellB> 0 </cellB>
                    </cellElem>
                  </cellMap>

    rule <k> testRegular(MAP, K1, V1, K2, V2) => done( partialMap(MAP) (partialInt(K1) |-> partialInt(V1)) (partialInt(K2) |-> partialInt(V2)) ) </k>

    rule <k> testCell(K1, A1, B1, K2, A2, B2) => done(.) </k>
         <cellMap>
          ( REST => <cellElem>
                        <key>   partialInt(K1) </key>
                        <cellA> partialInt(A1) </cellA>
                        <cellB> partialInt(B1) </cellB>
                    </cellElem>
                    <cellElem>
                        <key>   partialInt(K2) </key>
                        <cellA> partialInt(A2) </cellA>
                        <cellB> partialInt(B2) </cellB>
                    </cellElem>
                    REST )
         </cellMap>

    //to avoid warnings that function has no rules
    rule partialMap(.Map) => .Map
    rule partialInt(0) => 0

endmodule
