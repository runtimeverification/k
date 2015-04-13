// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST [Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"12"),#token(Int,"9"))]
  syntax priority 'x > 'y 'z > 'm 't > 'u
  syntax associativity right 'u
  syntax associativity left 'm 't
  syntax Foo ::= "z" [#klabel(#token(KString,"z")) Location(#token(Int,"6"),#token(Int,"18"),#token(Int,"6"),#token(Int,"20"))]
  syntax Foo ::= "y" [#klabel(#token(KString,"y")) Location(#token(Int,"5"),#token(Int,"18"),#token(Int,"5"),#token(Int,"40")) someattribute(#token(AttributeValue,""))]
  syntax Foo ::= "x" [#klabel(#token(KString,"x")) Location(#token(Int,"4"),#token(Int,"18"),#token(Int,"4"),#token(Int,"20"))]
  syntax Foo ::= "u" [#klabel(#token(KString,"u")) Location(#token(Int,"11"),#token(Int,"18"),#token(Int,"11"),#token(Int,"29")) off(#token(AttributeValue,""))]
  syntax Foo ::= "t" [#klabel(#token(KString,"t")) Location(#token(Int,"8"),#token(Int,"18"),#token(Int,"8"),#token(Int,"36")) andanohter(#token(AttributeValue,""))]
  syntax Foo ::= "m" [#klabel(#token(KString,"m")) Location(#token(Int,"9"),#token(Int,"18"),#token(Int,"9"),#token(Int,"20"))]
endmodule
