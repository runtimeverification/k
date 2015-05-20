// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST [Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"13"),#token(Int,"9")) Source(#token(KString,"src/test/resources/convertor-tests/syntaxWithPriorities.k"))]
  syntax priority x > y z > t > u
  syntax associativity right y
  syntax associativity left x
  syntax Foo ::= "z" [Location(#token(Int,"6"),#token(Int,"18"),#token(Int,"6"),#token(Int,"20")) Source(#token(KString,"src/test/resources/convertor-tests/syntaxWithPriorities.k")) klabel(#token(KString,"z"))]
  syntax Foo ::= "y" [Location(#token(Int,"5"),#token(Int,"18"),#token(Int,"5"),#token(Int,"40")) Source(#token(KString,"src/test/resources/convertor-tests/syntaxWithPriorities.k")) klabel(#token(KString,"y")) someattribute(#token(AttributeValue,""))]
  syntax Foo ::= "x" [Location(#token(Int,"4"),#token(Int,"18"),#token(Int,"4"),#token(Int,"20")) Source(#token(KString,"src/test/resources/convertor-tests/syntaxWithPriorities.k")) klabel(#token(KString,"x"))]
  syntax Foo ::= "u" [Location(#token(Int,"8"),#token(Int,"18"),#token(Int,"8"),#token(Int,"29")) Source(#token(KString,"src/test/resources/convertor-tests/syntaxWithPriorities.k")) klabel(#token(KString,"u")) off(#token(AttributeValue,""))]
  syntax Foo ::= "t" [Location(#token(Int,"7"),#token(Int,"18"),#token(Int,"7"),#token(Int,"36")) Source(#token(KString,"src/test/resources/convertor-tests/syntaxWithPriorities.k")) andanohter(#token(AttributeValue,"")) klabel(#token(KString,"t"))]
endmodule
