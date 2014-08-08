module IMP-SYNTAX
imports AUTO-INCLUDED-MODULE
rule `'if(_)_else_`(GeneratedFreshVar20, GeneratedFreshVar1, GeneratedFreshVar2) => GeneratedFreshVar20 ~> #freezer(`'if(_)_else_`(HOLE, GeneratedFreshVar1, GeneratedFreshVar2)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar20),#token{"#Bool","true"})
rule GeneratedFreshVar20 ~> #freezer(`'if(_)_else_`(HOLE, GeneratedFreshVar1, GeneratedFreshVar2)) => `'if(_)_else_`(GeneratedFreshVar20, GeneratedFreshVar1, GeneratedFreshVar2) when `isKResult`(GeneratedFreshVar20)
rule `'_=_;`(GeneratedFreshVar3, GeneratedFreshVar21) => GeneratedFreshVar21 ~> #freezer(`'_=_;`(GeneratedFreshVar3, HOLE)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar21),#token{"#Bool","true"})
rule GeneratedFreshVar21 ~> #freezer(`'_=_;`(GeneratedFreshVar3, HOLE)) => `'_=_;`(GeneratedFreshVar3, GeneratedFreshVar21) when `isKResult`(GeneratedFreshVar21)
rule `'!_`(GeneratedFreshVar22) => GeneratedFreshVar22 ~> #freezer(`'!_`(HOLE)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar22),#token{"#Bool","true"})
rule GeneratedFreshVar22 ~> #freezer(`'!_`(HOLE)) => `'!_`(GeneratedFreshVar22) when `isKResult`(GeneratedFreshVar22)
rule `'_+_`(GeneratedFreshVar23, GeneratedFreshVar7) => GeneratedFreshVar23 ~> #freezer(`'_+_`(HOLE, GeneratedFreshVar7)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar23),#token{"#Bool","true"})
rule GeneratedFreshVar23 ~> #freezer(`'_+_`(HOLE, GeneratedFreshVar7)) => `'_+_`(GeneratedFreshVar23, GeneratedFreshVar7) when `isKResult`(GeneratedFreshVar23)
rule `'_+_`(GeneratedFreshVar8, GeneratedFreshVar24) => GeneratedFreshVar24 ~> #freezer(`'_+_`(GeneratedFreshVar8, HOLE)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar24),#token{"#Bool","true"})
rule GeneratedFreshVar24 ~> #freezer(`'_+_`(GeneratedFreshVar8, HOLE)) => `'_+_`(GeneratedFreshVar8, GeneratedFreshVar24) when `isKResult`(GeneratedFreshVar24)
rule `'_/_`(GeneratedFreshVar25, GeneratedFreshVar11) => GeneratedFreshVar25 ~> #freezer(`'_/_`(HOLE, GeneratedFreshVar11)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar25),#token{"#Bool","true"})
rule GeneratedFreshVar25 ~> #freezer(`'_/_`(HOLE, GeneratedFreshVar11)) => `'_/_`(GeneratedFreshVar25, GeneratedFreshVar11) when `isKResult`(GeneratedFreshVar25)
rule `'_/_`(GeneratedFreshVar12, GeneratedFreshVar26) => GeneratedFreshVar26 ~> #freezer(`'_/_`(GeneratedFreshVar12, HOLE)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar26),#token{"#Bool","true"})
rule GeneratedFreshVar26 ~> #freezer(`'_/_`(GeneratedFreshVar12, HOLE)) => `'_/_`(GeneratedFreshVar12, GeneratedFreshVar26) when `isKResult`(GeneratedFreshVar26)
rule `'_&&_`(GeneratedFreshVar27, GeneratedFreshVar15) => GeneratedFreshVar27 ~> #freezer(`'_&&_`(HOLE, GeneratedFreshVar15)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar27),#token{"#Bool","true"})
rule GeneratedFreshVar27 ~> #freezer(`'_&&_`(HOLE, GeneratedFreshVar15)) => `'_&&_`(GeneratedFreshVar27, GeneratedFreshVar15) when `isKResult`(GeneratedFreshVar27)
rule `'_<=_`(GeneratedFreshVar28, GeneratedFreshVar17) => GeneratedFreshVar28 ~> #freezer(`'_<=_`(HOLE, GeneratedFreshVar17)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar28),#token{"#Bool","true"})
rule GeneratedFreshVar28 ~> #freezer(`'_<=_`(HOLE, GeneratedFreshVar17)) => `'_<=_`(GeneratedFreshVar28, GeneratedFreshVar17) when `isKResult`(GeneratedFreshVar28)
rule `'_<=_`(GeneratedFreshVar18, GeneratedFreshVar29) => GeneratedFreshVar29 ~> #freezer(`'_<=_`(GeneratedFreshVar18, HOLE)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar29),#token{"#Bool","true"})
rule GeneratedFreshVar29 ~> #freezer(`'_<=_`(GeneratedFreshVar18, HOLE)) => `'_<=_`(GeneratedFreshVar18, GeneratedFreshVar29) when `isKResult`(GeneratedFreshVar29)
endmodule
module IMP
imports AUTO-INCLUDED-MODULE
imports IMP-SYNTAX
configuration <T><k>$PGM:Pgm</k><state>`'.Map`()</state></T>
rule <k>X:Id => I...</k><state>...`'_|->_`(X, I)...</state>
rule `'_/_`(I1, I2) => `'_/Int_`(I1, I2) when `'_=/=Int_`(I2, #token{"#Int","0"})
rule `'_+_`(I1, I2) => `'_+Int_`(I1, I2)
rule `'_<=_`(I1, I2) => `'_<=Int_`(I1, I2)
rule `'!_`(T) => `'notBool_`(T)
rule `'_&&_`(#token{"#Bool","true"}, B) => B
rule `'_&&_`(#token{"#Bool","false"}, _) => #token{"#Bool","false"}
rule `'{}`() => .K
rule `'{_}`(S) => S
rule <k>`'_=_;`(X, I:Int) => .K...</k><state>...`'_|->_`(X, _ => I)...</state>
rule `'__`(S1:Stmt, S2:Stmt) => S1 ~> S2
rule `'if(_)_else_`(#token{"#Bool","true"}, S, _) => S
rule `'if(_)_else_`(#token{"#Bool","false"}, _, S) => S
rule `'while(_)_`(B, S) => `'if(_)_else_`(B, `'{_}`(`'__`(S, `'while(_)_`(B, S))), `'{}`())
rule <k>`'int_;_`(`_,Ids_`(X, Xs) => Xs, _)</k><state>`'_Map_`(Rho:Map, `'.Map`() => `'_|->_`(X, #token{"#Int","0"}))</state> when `'notBool_`(`'_in_`(X, `'keys`(Rho)))
rule `'int_;_`(`.Ids`(), S) => S
rule `'if(_)_else_`(GeneratedFreshVar20, GeneratedFreshVar1, GeneratedFreshVar2) => GeneratedFreshVar20 ~> #freezer(`'if(_)_else_`(HOLE, GeneratedFreshVar1, GeneratedFreshVar2)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar20),#token{"#Bool","true"})
rule GeneratedFreshVar20 ~> #freezer(`'if(_)_else_`(HOLE, GeneratedFreshVar1, GeneratedFreshVar2)) => `'if(_)_else_`(GeneratedFreshVar20, GeneratedFreshVar1, GeneratedFreshVar2) when `isKResult`(GeneratedFreshVar20)
rule `'_=_;`(GeneratedFreshVar3, GeneratedFreshVar21) => GeneratedFreshVar21 ~> #freezer(`'_=_;`(GeneratedFreshVar3, HOLE)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar21),#token{"#Bool","true"})
rule GeneratedFreshVar21 ~> #freezer(`'_=_;`(GeneratedFreshVar3, HOLE)) => `'_=_;`(GeneratedFreshVar3, GeneratedFreshVar21) when `isKResult`(GeneratedFreshVar21)
rule `'!_`(GeneratedFreshVar22) => GeneratedFreshVar22 ~> #freezer(`'!_`(HOLE)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar22),#token{"#Bool","true"})
rule GeneratedFreshVar22 ~> #freezer(`'!_`(HOLE)) => `'!_`(GeneratedFreshVar22) when `isKResult`(GeneratedFreshVar22)
rule `'_+_`(GeneratedFreshVar23, GeneratedFreshVar7) => GeneratedFreshVar23 ~> #freezer(`'_+_`(HOLE, GeneratedFreshVar7)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar23),#token{"#Bool","true"})
rule GeneratedFreshVar23 ~> #freezer(`'_+_`(HOLE, GeneratedFreshVar7)) => `'_+_`(GeneratedFreshVar23, GeneratedFreshVar7) when `isKResult`(GeneratedFreshVar23)
rule `'_+_`(GeneratedFreshVar8, GeneratedFreshVar24) => GeneratedFreshVar24 ~> #freezer(`'_+_`(GeneratedFreshVar8, HOLE)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar24),#token{"#Bool","true"})
rule GeneratedFreshVar24 ~> #freezer(`'_+_`(GeneratedFreshVar8, HOLE)) => `'_+_`(GeneratedFreshVar8, GeneratedFreshVar24) when `isKResult`(GeneratedFreshVar24)
rule `'_/_`(GeneratedFreshVar25, GeneratedFreshVar11) => GeneratedFreshVar25 ~> #freezer(`'_/_`(HOLE, GeneratedFreshVar11)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar25),#token{"#Bool","true"})
rule GeneratedFreshVar25 ~> #freezer(`'_/_`(HOLE, GeneratedFreshVar11)) => `'_/_`(GeneratedFreshVar25, GeneratedFreshVar11) when `isKResult`(GeneratedFreshVar25)
rule `'_/_`(GeneratedFreshVar12, GeneratedFreshVar26) => GeneratedFreshVar26 ~> #freezer(`'_/_`(GeneratedFreshVar12, HOLE)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar26),#token{"#Bool","true"})
rule GeneratedFreshVar26 ~> #freezer(`'_/_`(GeneratedFreshVar12, HOLE)) => `'_/_`(GeneratedFreshVar12, GeneratedFreshVar26) when `isKResult`(GeneratedFreshVar26)
rule `'_&&_`(GeneratedFreshVar27, GeneratedFreshVar15) => GeneratedFreshVar27 ~> #freezer(`'_&&_`(HOLE, GeneratedFreshVar15)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar27),#token{"#Bool","true"})
rule GeneratedFreshVar27 ~> #freezer(`'_&&_`(HOLE, GeneratedFreshVar15)) => `'_&&_`(GeneratedFreshVar27, GeneratedFreshVar15) when `isKResult`(GeneratedFreshVar27)
rule `'_<=_`(GeneratedFreshVar28, GeneratedFreshVar17) => GeneratedFreshVar28 ~> #freezer(`'_<=_`(HOLE, GeneratedFreshVar17)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar28),#token{"#Bool","true"})
rule GeneratedFreshVar28 ~> #freezer(`'_<=_`(HOLE, GeneratedFreshVar17)) => `'_<=_`(GeneratedFreshVar28, GeneratedFreshVar17) when `isKResult`(GeneratedFreshVar28)
rule `'_<=_`(GeneratedFreshVar18, GeneratedFreshVar29) => GeneratedFreshVar29 ~> #freezer(`'_<=_`(GeneratedFreshVar18, HOLE)) when `'_=/=K_`(`isKResult`(GeneratedFreshVar29),#token{"#Bool","true"})
rule GeneratedFreshVar29 ~> #freezer(`'_<=_`(GeneratedFreshVar18, HOLE)) => `'_<=_`(GeneratedFreshVar18, GeneratedFreshVar29) when `isKResult`(GeneratedFreshVar29)
endmodule
