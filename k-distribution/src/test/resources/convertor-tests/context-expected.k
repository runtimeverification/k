// Copyright (c) 2014-2015 K Team. All Rights Reserved.
Require(include.k)

module INCLUDE [org.kframework.attributes.Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"12"),#token(Int,"9"))]
  syntax String ::= #String [org.kframework.attributes.Location(#token(Int,"6"),#token(Int,"21"),#token(Int,"6"),#token(Int,"27"))]
  syntax Map ::= ".Map" [function(#token(AttributeValue,"")) hook(#token(AttributeValue,"Map:.Map")) org.kframework.attributes.Location(#token(Int,"8"),#token(Int,"18"),#token(Int,"8"),#token(Int,"74"))]
  syntax #String ::= r"\"\\\"\" ((~[\\\"\\n\\r\\\\]) | (((([\\\\][nrtf\\\"\\\\]) | ([\\\\][x][0-9a-fA-F][0-9a-fA-F])) | ([\\\\][u][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])) | ([\\\\][U][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])))* \"\\\"\"" [org.kframework.attributes.Location(#token(Int,"4"),#token(Int,"22"),#token(Int,"5"),#token(Int,"166")) regex(#token(AttributeValue,"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]"))]
  syntax #Bool ::= "true" [org.kframework.attributes.Location(#token(Int,"10"),#token(Int,"20"),#token(Int,"10"),#token(Int,"25"))]
  syntax #Bool ::= "false" [org.kframework.attributes.Location(#token(Int,"11"),#token(Int,"20"),#token(Int,"11"),#token(Int,"26"))]
endmodule


module TEST [org.kframework.attributes.Location(#token(Int,"5"),#token(Int,"1"),#token(Int,"13"),#token(Int,"9"))]
  syntax Exp ::= Exp "+" Exp [org.kframework.attributes.Location(#token(Int,"8"),#token(Int,"18"),#token(Int,"8"),#token(Int,"28"))]
  imports INCLUDE [org.kframework.attributes.Location(#token(Int,"6"),#token(Int,"3"),#token(Int,"6"),#token(Int,"17"))]
  context '_+_(_,HOLE(#token(KItem,""))) requires #token(Bool,"true")
  context '_+_(HOLE(#token(KItem,"")),_) requires #token(Bool,"true")
endmodule
