// Copyright (c) 2014-2019 K Team. All Rights Reserved.
module TEST [Location(#token("3",Int),#token("1",Int),#token("10",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/complex.k",KString))]
  syntax Bool ::= #Bool [Location(#token("6",Int),#token("19",Int),#token("6",Int),#token("23",Int)) Source(#token("src/test/resources/convertor-tests/complex.k",KString))]
  syntax #Bool ::= "true" [Location(#token("4",Int),#token("20",Int),#token("4",Int),#token("25",Int)) Source(#token("src/test/resources/convertor-tests/complex.k",KString)) klabel(#token("true",KString))]
  syntax #Bool ::= "false" [Location(#token("5",Int),#token("20",Int),#token("5",Int),#token("26",Int)) Source(#token("src/test/resources/convertor-tests/complex.k",KString)) klabel(#token("false",KString))]
  rule =>(#token("true",#Bool),INJECTED-KLIST()) requires _andBool_(#token("true",Bool),#token("true",Bool)) ensures #token("true",Bool) [Location(#token("8",Int),#token("3",Int),#token("8",Int),#token("21",Int)) Source(#token("src/test/resources/convertor-tests/complex.k",KString))]
  rule =>(#token("true",#Bool),INJECTED-KLIST(#token("true",#Bool))) requires _andBool_(#token("true",Bool),#token("true",Bool)) ensures #token("true",Bool) [Location(#token("9",Int),#token("3",Int),#token("9",Int),#token("29",Int)) Source(#token("src/test/resources/convertor-tests/complex.k",KString))]
endmodule
