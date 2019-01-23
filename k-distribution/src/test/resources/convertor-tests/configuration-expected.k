// Copyright (c) 2014-2019 K Team. All Rights Reserved.
module INCLUDE [Location(#token("3",Int),#token("1",Int),#token("12",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/include.k",KString))]
  syntax String ::= #String [Location(#token("6",Int),#token("21",Int),#token("6",Int),#token("27",Int)) Source(#token("src/test/resources/convertor-tests/include.k",KString))]
  syntax Map ::= ".Map" [Location(#token("8",Int),#token("18",Int),#token("8",Int),#token("74",Int)) Source(#token("src/test/resources/convertor-tests/include.k",KString)) function(#token("",AttributeValue)) hook(#token("Map:.Map",AttributeValue)) klabel(#token(".Map",KString))]
  syntax #String ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]" [Location(#token("4",Int),#token("22",Int),#token("5",Int),#token("166",Int)) Source(#token("src/test/resources/convertor-tests/include.k",KString)) klabel(#token("",KString)) regex(#token("[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]",AttributeValue))]
  syntax #Bool ::= "true" [Location(#token("10",Int),#token("20",Int),#token("10",Int),#token("25",Int)) Source(#token("src/test/resources/convertor-tests/include.k",KString)) klabel(#token("true",KString))]
  syntax #Bool ::= "false" [Location(#token("11",Int),#token("20",Int),#token("11",Int),#token("26",Int)) Source(#token("src/test/resources/convertor-tests/include.k",KString)) klabel(#token("false",KString))]
endmodule


module TEST [Location(#token("4",Int),#token("1",Int),#token("7",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/configuration.k",KString))]
  imports INCLUDE
  Configuration(t(KBag(k(.K),env(.Map()),stack(KBag()))),#token("true",Bool),[Location(#token("6",Int),#token("17",Int),#token("6",Int),#token("108",Int)) Source(#token("src/test/resources/convertor-tests/configuration.k",KString))])
endmodule
