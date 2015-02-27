// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [org.kframework.attributes.Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"12"),#token(Int,"9"))]
  syntax priority 'x > 'y 'z > 'm 't > 'u
  syntax associativity right 'u
  syntax associativity left 'm 't
  syntax Foo ::= "z" [org.kframework.attributes.Location(#token(Int,"6"),#token(Int,"18"),#token(Int,"6"),#token(Int,"20"))]
  syntax Foo ::= "y" [org.kframework.attributes.Location(#token(Int,"5"),#token(Int,"18"),#token(Int,"5"),#token(Int,"40")) someattribute(#token(AttributeValue,""))]
  syntax Foo ::= "x" [org.kframework.attributes.Location(#token(Int,"4"),#token(Int,"18"),#token(Int,"4"),#token(Int,"20"))]
  syntax Foo ::= "u" [off(#token(AttributeValue,"")) org.kframework.attributes.Location(#token(Int,"11"),#token(Int,"18"),#token(Int,"11"),#token(Int,"29"))]
  syntax Foo ::= "t" [andanohter(#token(AttributeValue,"")) org.kframework.attributes.Location(#token(Int,"8"),#token(Int,"18"),#token(Int,"8"),#token(Int,"36"))]
  syntax Foo ::= "m" [org.kframework.attributes.Location(#token(Int,"9"),#token(Int,"18"),#token(Int,"9"),#token(Int,"20"))]
endmodule
