// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [org.kframework.attributes.Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"10"),#token(Int,"9"))]
  syntax Bool ::= #Bool [org.kframework.attributes.Location(#token(Int,"6"),#token(Int,"19"),#token(Int,"6"),#token(Int,"23"))]
  syntax #Bool ::= "true" [org.kframework.attributes.Location(#token(Int,"4"),#token(Int,"20"),#token(Int,"4"),#token(Int,"25"))]
  syntax #Bool ::= "false" [org.kframework.attributes.Location(#token(Int,"5"),#token(Int,"20"),#token(Int,"5"),#token(Int,"26"))]
  rule #token(#Bool,"true")=>INJECTED-KLIST() requires '_andBool_(#token(Bool,"true"),#token(Bool,"true")) ensures #token(Bool,"true") [org.kframework.attributes.Location(#token(Int,"8"),#token(Int,"3"),#token(Int,"8"),#token(Int,"21"))]
  rule #token(#Bool,"true")=>INJECTED-KLIST(#token(#Bool,"true")) requires '_andBool_(#token(Bool,"true"),#token(Bool,"true")) ensures #token(Bool,"true") [org.kframework.attributes.Location(#token(Int,"9"),#token(Int,"3"),#token(Int,"9"),#token(Int,"29"))]
endmodule
