// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [org.kframework.attributes.Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"18"),#token(Int,"9"))]
  syntax Bools ::= Bools "," Bools [#klabel(#token(KString,"'_,_")) org.kframework.attributes.Location(#token(Int,"15"),#token(Int,"20"),#token(Int,"15"),#token(Int,"34")) userList(#token(KString,"Bools"))]
  syntax Bools ::= Bool [org.kframework.attributes.Location(#token(Int,"15"),#token(Int,"20"),#token(Int,"15"),#token(Int,"34")) userList(#token(KString,"Bools"))]
  syntax Bools ::= ".Bools" [#klabel(#token(KString,"'.List{\"'_,_\"}")) org.kframework.attributes.Location(#token(Int,"15"),#token(Int,"20"),#token(Int,"15"),#token(Int,"34")) userList(#token(KString,"Bools"))]
  syntax Bool ::= #Bool [org.kframework.attributes.Location(#token(Int,"6"),#token(Int,"19"),#token(Int,"6"),#token(Int,"23"))]
  syntax Bool ::= "notBool" Bool [org.kframework.attributes.Location(#token(Int,"8"),#token(Int,"19"),#token(Int,"8"),#token(Int,"32"))]
  syntax #Bool ::= "true" [org.kframework.attributes.Location(#token(Int,"4"),#token(Int,"20"),#token(Int,"4"),#token(Int,"25"))]
  syntax #Bool ::= "false" [org.kframework.attributes.Location(#token(Int,"5"),#token(Int,"20"),#token(Int,"5"),#token(Int,"26"))]
  rule 'notBool_(#token(#Bool,"true"))=>#token(#Bool,"false") requires '_andBool_(#token(Bool,"true"),#token(Bool,"true")) ensures #token(Bool,"true") [org.kframework.attributes.Location(#token(Int,"10"),#token(Int,"3"),#token(Int,"10"),#token(Int,"28"))]
  rule 'notBool_(#token(#Bool,"false"))=>#token(#Bool,"true") requires '_andBool_(#token(Bool,"true"),#token(Bool,"true")) ensures #token(Bool,"true") [org.kframework.attributes.Location(#token(Int,"11"),#token(Int,"3"),#token(Int,"11"),#token(Int,"28"))]
  rule 'notBool(#token(#Bool,"true"))=>#token(#Bool,"false") requires '_andBool_(#token(Bool,"true"),#token(Bool,"true")) ensures #token(Bool,"true") [org.kframework.attributes.Location(#token(Int,"13"),#token(Int,"3"),#token(Int,"13"),#token(Int,"30"))]
  rule '_,_(#token(#Bool,"true"),#token(#Bool,"true"))=>'.List{"'_,_"}() requires '_andBool_(#token(Bool,"true"),#token(Bool,"true")) ensures #token(Bool,"true") [org.kframework.attributes.Location(#token(Int,"17"),#token(Int,"3"),#token(Int,"17"),#token(Int,"27"))]
endmodule
