// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module INCLUDE [Location(#token("3",Int),#token("1",Int),#token("12",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/include.k",KString))]
  syntax String ::= #String [Location(#token("6",Int),#token("21",Int),#token("6",Int),#token("27",Int)) Source(#token("src/test/resources/convertor-tests/include.k",KString))]
  syntax Map ::= ".Map" [#klabel(#token(".Map",KString)) Location(#token("8",Int),#token("18",Int),#token("8",Int),#token("74",Int)) Source(#token("src/test/resources/convertor-tests/include.k",KString)) function(#token("",AttributeValue)) hook(#token("Map:.Map",AttributeValue))]
  syntax #String ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]" [#klabel(#token("",KString)) Location(#token("4",Int),#token("22",Int),#token("5",Int),#token("166",Int)) Source(#token("src/test/resources/convertor-tests/include.k",KString)) regex(#token("[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]",AttributeValue))]
  syntax #Bool ::= "true" [#klabel(#token("true",KString)) Location(#token("10",Int),#token("20",Int),#token("10",Int),#token("25",Int)) Source(#token("src/test/resources/convertor-tests/include.k",KString))]
  syntax #Bool ::= "false" [#klabel(#token("false",KString)) Location(#token("11",Int),#token("20",Int),#token("11",Int),#token("26",Int)) Source(#token("src/test/resources/convertor-tests/include.k",KString))]
endmodule


module TEST [Location(#token("5",Int),#token("1",Int),#token("13",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/context.k",KString))]
  imports INCLUDE
  syntax Exp ::= Exp "+" Exp [#klabel(#token("_+_",KString)) Location(#token("8",Int),#token("18",Int),#token("8",Int),#token("28",Int)) Source(#token("src/test/resources/convertor-tests/context.k",KString))]
  context _+_(_,HOLE(#token("",KItem))) requires #token("true",Bool)
  context _+_(HOLE(#token("",KItem)),_) requires #token("true",Bool)
endmodule
