module TEST
//  syntax #Int ::= Token{[\-\+]? [0-9]+} [regex("[\\+-]?\\d+"), prefer]
//  syntax Int ::= #Int
//  syntax Id ::= Token{[A-Za-z\_][A-Za-z0-9\_]*} [notInRules, regex("(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*")]
//  syntax #Bool ::= Token{"true"}
//  syntax #Bool ::= Token{"false"}
//  syntax Bool ::= #Bool
    syntax Foo ::= "a" [klabel('a)]
    syntax Foo ::= "b" [klabel('b)]
    rule a => b
//  syntax #String ::= Token{"\"" ((~[\"\n\r\\]) | (((([\\][nrtf\"\\]) | ([\\][x][0-9a-fA-F][0-9a-fA-F])) | ([\\][u][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])) | ([\\][U][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])))* "\""}
//                     [regex("[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]")]
//  syntax String ::= #String
//
//  syntax priority '(_) ++_
//    > -_
//    > _*_ _%_ _/_
//    > _+_ _-_
//    > _>=_ _==_ _!=_ _<=_ _>_ _<_
//    > !_
//    > _&&_ _||_
//
//  syntax Exp ::= Int
//  syntax Exp ::= Bool
//  syntax Exp ::= String
//  syntax Exp ::= Id
//  syntax Exp ::= "(" Exp ")"             [bracket]
//  syntax Exp ::= "++" Exp                [klabel(++_)]
//  syntax Exp ::= "-" Exp                 [strict, klabel(-_)]
//  syntax Exp ::= Exp "*" Exp             [strict, left, klabel(_*_)]
//  syntax Exp ::= Exp "/" Exp             [strict, left, klabel(_/_)]
//  syntax Exp ::= Exp "%" Exp             [strict, left, klabel(_%_)]
//  syntax Exp ::= Exp "+" Exp             [strict, left, klabel(_+_)]
//  syntax Exp ::= Exp "-" Exp             [strict, left, klabel(_-_)]
//  syntax Exp ::= Exp "<" Exp             [strict, non-assoc, klabel(_<_)]
//  syntax Exp ::= Exp "<=" Exp            [strict, non-assoc, klabel(_<=_)]
//  syntax Exp ::= Exp ">" Exp             [strict, non-assoc, klabel(_>_)]
//  syntax Exp ::= Exp ">=" Exp            [strict, non-assoc, klabel(_>=_)]
//  syntax Exp ::= Exp "==" Exp            [strict, non-assoc, klabel(_==_)]
//  syntax Exp ::= Exp "!=" Exp            [strict, non-assoc, klabel(_!=_)]
//  syntax Exp ::= "!" Exp                 [strict, klabel(!_)]
//  syntax Exp ::= Exp "&&" Exp            [strict(1), left, klabel(_&&_)]
//  syntax Exp ::= Exp "||" Exp            [strict(1), left, klabel(_||_)]
endmodule