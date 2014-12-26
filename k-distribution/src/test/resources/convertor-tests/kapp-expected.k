// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST [location(startLine(#token(Int,"3")),startColumn(#token(Int,"1")),endLine(#token(Int,"18")),endColumn(#token(Int,"9")))]
  syntax Bools ::= Bools "," Bools [userList(Bools)]
  syntax Bools ::= Bool [userList(Bools)]
  syntax Bools ::= ".Bools" [userList(Bools)]
  syntax Bool ::= #Bool [location(startLine(#token(Int,"6")),startColumn(#token(Int,"19")),endLine(#token(Int,"6")),endColumn(#token(Int,"23")))]
  syntax Bool ::= "notBool" Bool [location(startLine(#token(Int,"8")),startColumn(#token(Int,"19")),endLine(#token(Int,"8")),endColumn(#token(Int,"32")))]
  syntax #Bool ::= "true" [location(startLine(#token(Int,"4")),startColumn(#token(Int,"20")),endLine(#token(Int,"4")),endColumn(#token(Int,"25")))]
  syntax #Bool ::= "false" [location(startLine(#token(Int,"5")),startColumn(#token(Int,"20")),endLine(#token(Int,"5")),endColumn(#token(Int,"26")))]
  rule 'notBool_(#token(#Bool,"true")) [location(startLine(#token(Int,"10")),startColumn(#token(Int,"8")),endLine(#token(Int,"10")),endColumn(#token(Int,"20"))) sort(Bool)]=>#token(#Bool,"false") requires #token(KBoolean,"true") ensures #token(KBoolean,"true") [location(startLine(#token(Int,"10")),startColumn(#token(Int,"3")),endLine(#token(Int,"10")),endColumn(#token(Int,"28")))]
  rule 'notBool_(#token(#Bool,"false")) [location(startLine(#token(Int,"11")),startColumn(#token(Int,"8")),endLine(#token(Int,"11")),endColumn(#token(Int,"21"))) sort(Bool)]=>#token(#Bool,"true") requires #token(KBoolean,"true") ensures #token(KBoolean,"true") [location(startLine(#token(Int,"11")),startColumn(#token(Int,"3")),endLine(#token(Int,"11")),endColumn(#token(Int,"28")))]
  rule 'notBool(#token(#Bool,"true")) [location(startLine(#token(Int,"13")),startColumn(#token(Int,"8")),endLine(#token(Int,"13")),endColumn(#token(Int,"22")))]=>#token(#Bool,"false") requires #token(KBoolean,"true") ensures #token(KBoolean,"true") [location(startLine(#token(Int,"13")),startColumn(#token(Int,"3")),endLine(#token(Int,"13")),endColumn(#token(Int,"30")))]
  rule '_,_(#token(#Bool,"true"),#token(#Bool,"true")) [location(startLine(#token(Int,"17")),startColumn(#token(Int,"8")),endLine(#token(Int,"17")),endColumn(#token(Int,"18"))) sort(Bools)]=>'.List{"'_,_"}() [listTerminator()] requires #token(KBoolean,"true") ensures #token(KBoolean,"true") [location(startLine(#token(Int,"17")),startColumn(#token(Int,"3")),endLine(#token(Int,"17")),endColumn(#token(Int,"27")))]
endmodule
