// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module INCLUDE [Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"12"),#token(Int,"9")) Source(#token(KString,"src/test/resources/convertor-tests/include.k"))]
  syntax String ::= #String [Location(#token(Int,"6"),#token(Int,"21"),#token(Int,"6"),#token(Int,"27")) Source(#token(KString,"src/test/resources/convertor-tests/include.k"))]
  syntax Map ::= ".Map" [Location(#token(Int,"8"),#token(Int,"18"),#token(Int,"8"),#token(Int,"74")) Source(#token(KString,"src/test/resources/convertor-tests/include.k")) function(#token(AttributeValue,"")) hook(#token(AttributeValue,"Map:.Map")) klabel(#token(KString,".Map"))]
  syntax #String ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]" [Location(#token(Int,"4"),#token(Int,"22"),#token(Int,"5"),#token(Int,"166")) Source(#token(KString,"src/test/resources/convertor-tests/include.k")) klabel(#token(KString,"")) regex(#token(AttributeValue,"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]"))]
  syntax #Bool ::= "true" [Location(#token(Int,"10"),#token(Int,"20"),#token(Int,"10"),#token(Int,"25")) Source(#token(KString,"src/test/resources/convertor-tests/include.k")) klabel(#token(KString,"true"))]
  syntax #Bool ::= "false" [Location(#token(Int,"11"),#token(Int,"20"),#token(Int,"11"),#token(Int,"26")) Source(#token(KString,"src/test/resources/convertor-tests/include.k")) klabel(#token(KString,"false"))]
endmodule


module TEST [Location(#token(Int,"5"),#token(Int,"1"),#token(Int,"13"),#token(Int,"9")) Source(#token(KString,"src/test/resources/convertor-tests/context.k"))]
  imports INCLUDE
  syntax Exp ::= Exp "+" Exp [Location(#token(Int,"8"),#token(Int,"18"),#token(Int,"8"),#token(Int,"28")) Source(#token(KString,"src/test/resources/convertor-tests/context.k")) klabel(#token(KString,"_+_"))]
  context _+_(_,HOLE(#token(KItem,""))) requires #token(Bool,"true")
  context _+_(HOLE(#token(KItem,"")),_) requires #token(Bool,"true")
endmodule
