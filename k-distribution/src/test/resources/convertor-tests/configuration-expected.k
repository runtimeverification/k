// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module INCLUDE [Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"12"),#token(Int,"9")) Source(#token(KString,"src/test/resources/convertor-tests/include.k"))]
  syntax String ::= #String [Location(#token(Int,"6"),#token(Int,"21"),#token(Int,"6"),#token(Int,"27")) Source(#token(KString,"src/test/resources/convertor-tests/include.k"))]
  syntax Map ::= ".Map" [Location(#token(Int,"8"),#token(Int,"18"),#token(Int,"8"),#token(Int,"74")) Source(#token(KString,"src/test/resources/convertor-tests/include.k")) function(#token(AttributeValue,"")) hook(#token(AttributeValue,"Map:.Map")) klabel(#token(KString,".Map"))]
  syntax #String ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]" [Location(#token(Int,"4"),#token(Int,"22"),#token(Int,"5"),#token(Int,"166")) Source(#token(KString,"src/test/resources/convertor-tests/include.k")) regex(#token(AttributeValue,"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]")) klabel(#token(KString,""))]
  syntax #Bool ::= "true" [Location(#token(Int,"10"),#token(Int,"20"),#token(Int,"10"),#token(Int,"25")) Source(#token(KString,"src/test/resources/convertor-tests/include.k")) klabel(#token(KString,"true"))]
  syntax #Bool ::= "false" [Location(#token(Int,"11"),#token(Int,"20"),#token(Int,"11"),#token(Int,"26")) Source(#token(KString,"src/test/resources/convertor-tests/include.k")) klabel(#token(KString,"false"))]
endmodule


module TEST [Location(#token(Int,"4"),#token(Int,"1"),#token(Int,"7"),#token(Int,"9")) Source(#token(KString,"src/test/resources/convertor-tests/configuration.k"))]
  imports INCLUDE
  Configuration(t(KBag(k(.K),env(.Map()),stack(KBag()))),#token(Bool,"true"),[Location(#token(Int,"6"),#token(Int,"17"),#token(Int,"6"),#token(Int,"108")) Source(#token(KString,"src/test/resources/convertor-tests/configuration.k"))])
endmodule
