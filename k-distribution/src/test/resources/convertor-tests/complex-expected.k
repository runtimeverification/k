// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [location(startLine(#token(Int,"3")),startColumn(#token(Int,"1")),endLine(#token(Int,"10")),endColumn(#token(Int,"9")))]
  syntax Bool ::= #Bool [location(startLine(#token(Int,"6")),startColumn(#token(Int,"19")),endLine(#token(Int,"6")),endColumn(#token(Int,"23")))]
  syntax #Bool ::= "true" [location(startLine(#token(Int,"4")),startColumn(#token(Int,"20")),endLine(#token(Int,"4")),endColumn(#token(Int,"25")))]
  syntax #Bool ::= "false" [location(startLine(#token(Int,"5")),startColumn(#token(Int,"20")),endLine(#token(Int,"5")),endColumn(#token(Int,"26")))]
  rule #token(#Bool,"true")=>#klist(KList(#token(#Bool,"true"))) requires #token(KBoolean,"true") ensures #token(KBoolean,"true") [location(startLine(#token(Int,"9")),startColumn(#token(Int,"3")),endLine(#token(Int,"9")),endColumn(#token(Int,"29")))]
  rule #token(#Bool,"true")=>#klist(.K) requires #token(KBoolean,"true") ensures #token(KBoolean,"true") [location(startLine(#token(Int,"8")),startColumn(#token(Int,"3")),endLine(#token(Int,"8")),endColumn(#token(Int,"21")))]
endmodule
