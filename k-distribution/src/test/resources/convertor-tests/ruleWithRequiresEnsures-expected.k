// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [org.kframework.attributes.Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"9"),#token(Int,"9"))]
  syntax Exp [org.kframework.attributes.Location(#token(Int,"4"),#token(Int,"3"),#token(Int,"4"),#token(Int,"12"))]
  rule A=>A requires A ensures A [org.kframework.attributes.Location(#token(Int,"8"),#token(Int,"3"),#token(Int,"8"),#token(Int,"38"))]
  rule A=>A requires A ensures #token(KBoolean,"true") [org.kframework.attributes.Location(#token(Int,"6"),#token(Int,"3"),#token(Int,"6"),#token(Int,"28"))]
  rule A=>A requires #token(KBoolean,"true") ensures A [org.kframework.attributes.Location(#token(Int,"7"),#token(Int,"3"),#token(Int,"7"),#token(Int,"27"))]
endmodule
