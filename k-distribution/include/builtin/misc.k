// Copyright (c) 2015 K Team. All Rights Reserved.

module ID
  syntax Id ::= r"(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*"     [token, autoReject]
endmodule

module EMPTY-ID
  imports K
  imports LOGIC

  syntax Id
  syntax KBool ::= "isId" "(" K ")"         [klabel(isId), function]
endmodule

module BOOL
  syntax Bool ::= "true"           [token]
  syntax Bool ::= "false"          [token]
endmodule

module LOGIC
  syntax KBool ::= "KTrue"                  [klabel(_andBool_), function, hook(#BOOL:_andBool_)]
  syntax KBool ::= "KFalse"                 [klabel(_orBool_), function, hook(#BOOL:_orBool_)]

  syntax KBool ::= "notBool" "(" KBool ")"  [klabel(notBool_),  function, hook(#BOOL:notBool_)]
  syntax KBool ::= KBool "andBool" KBool    [klabel('_andBool_), function, hook(#BOOL:_andBool_), left]

  syntax priority 'notBool_ > '_andBool_
endmodule

module INT
  imports K
  imports LOGIC

  syntax Int ::= r"[\\+-]?[0-9]+"     [prefer, token]

  syntax Int ::= Int "+Int" Int     [klabel('_+Int_), function, hook(#INT:_+Int_), left]
  syntax Int ::= Int "-Int" Int     [klabel('_-Int_), function, hook(#INT:_-Int_), left]
  syntax Int ::= Int "*Int" Int     [klabel('_*Int_), function, hook(#INT:_*Int_), left]
  syntax Int ::= Int "/Int" Int     [klabel('_/Int_), function, hook(#INT:_/Int_), left]
  syntax Int ::= Int "%Int" Int     [klabel('_%Int_), function, hook(#INT:_%Int_), left]

  syntax KBool ::= Int "<=Int" Int       [klabel('_<=Int_), function, hook(#INT:_<=Int_), left]
  syntax KBool ::= Int "<Int" Int        [klabel('_<Int_),  function, hook(#INT:_<Int_),  left]
  syntax KBool ::= Int ">=Int" Int       [klabel('_>=Int_), function, hook(#INT:_>=Int_), left]
  syntax KBool ::= Int ">Int" Int        [klabel('_>Int_),  function, hook(#INT:_>Int_),  left]

  syntax priority '_*Int_ '_/Int_ '_%Int_ > '_+Int_ '_-Int_

  syntax KBool ::= "isInt" "(" K ")"     [klabel(isKResult), function]
endmodule

module K-RESULT
  import BASIC-K
  import LOGIC

  syntax KResult
  syntax KBool ::= isKResult(K) [function,klabel(isKResult)]
endmodule

module STRICTNESS
  syntax KBott  ::= "[]"           [klabel([])]
endmodule

module MAP
  imports SET
  imports K

  syntax Map ::= Map Map        [klabel('_Map_), function, assoc, comm, hook(Map:__)]
  syntax Map ::= ".Map"         [klabel('_Map_),  function, hook(Map:.Map)]
  syntax Map ::= K "|->" K      [klabel('_|->_), function, hook(Map:_|->_)]
  syntax priorities '_|->_ > '_Map_

  syntax Set ::= "keys" "(" Map ")"     [klabel('keys), function, hook(Map:keys)]

  syntax K ::= Map "[" K "]"                    [function, klabel(Map:lookup)]
endmodule

module SET
  imports LOGIC
  imports K

  syntax Set

  syntax KBool ::= K "in" Set            [klabel('_in_), function, hook(Set:in)]
endmodule
