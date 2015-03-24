// Copyright (c) 2015 K Team. All Rights Reserved.

module ID
  syntax Id ::= r"(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*"     [notInRules, token, autoreject]
endmodule

module EMPTY-ID
  imports K
  imports BOOL

  syntax Id
  syntax Bool ::= "isId" "(" K ")"         [klabel(isId), function]
endmodule

module BOOL
  syntax Bool ::= "true"           [klabel(_andBool_), function, hook(#BOOL:_andBool_)]
  syntax Bool ::= "false"          [klabel(_orBool_), function, hook(#BOOL:_orBool_)]

  syntax Bool ::= "notBool" "(" Bool ")"    [klabel(notBool_),  function, hook(#BOOL:notBool_)]
  syntax Bool ::= Bool "andBool" Bool       [klabel('_andBool_), function, hook(#BOOL:_andBool_), left]

  syntax priority 'notBool_ > '_andBool_
endmodule

module INT
  imports BOOL
  imports K

  syntax Int ::= r"[\\+-]?\\d+"     [prefer, token]

  syntax Int ::= Int "+Int" Int     [klabel('_+Int_), function, hook(#INT:_+Int_), left]
  syntax Int ::= Int "-Int" Int     [klabel('_-Int_), function, hook(#INT:_-Int_), left]
  syntax Int ::= Int "*Int" Int     [klabel('_*Int_), function, hook(#INT:_*Int_), left]
  syntax Int ::= Int "/Int" Int     [klabel('_/Int_), function, hook(#INT:_/Int_), left]
  syntax Int ::= Int "%Int" Int     [klabel('_%Int_), function, hook(#INT:_%Int_), left]

  syntax Bool ::= Int "<=Int" Int       [klabel('_<=Int_), function, hook(#INT:_<=Int_), left]
  syntax Bool ::= Int "<Int" Int        [klabel('_<Int_),  function, hook(#INT:_<Int_),  left]
  syntax Bool ::= Int ">=Int" Int       [klabel('_>=Int_), function, hook(#INT:_>=Int_), left]
  syntax Bool ::= Int ">Int" Int        [klabel('_>Int_),  function, hook(#INT:_>Int_),  left]

  syntax priority '_*Int_ '_/Int_ '_%Int_ > '_+Int_ '_-Int_

  syntax Bool ::= "isInt" "(" K ")"         [klabel(isKResult), function]
endmodule

module LOGIC
  syntax Boolean ::= "true"           [klabel(_andBool_), function, hook(#BOOL:_andBool_)]
                   | "false"          [klabel(_orBool_), function, hook(#BOOL:_orBool_)]

  syntax Boolean ::= "notBool" "(" Boolean ")"    [klabel(notBool_),  function, hook(#BOOL:notBool_)]
  syntax Boolean ::= Boolean "andBool" Boolean       [klabel('_andBool_), function, hook(#BOOL:_andBool_), left]
endmodule

module K-RESULT
  import BASIC-K
  import BOOL

  syntax KResult
  syntax Bool ::= isKResult(K) [function,klabel(isKResult)]
endmodule

module STRICTNESS
  syntax KBott  ::= "[]"           [klabel([])]
endmodule

module MAP
  imports SET
  imports K

  syntax Map ::= Map Map        [klabel('_Map_), function, hook(Map:__)]
  syntax Map ::= ".Map"         [klabel('_Map_),  function, hook(Map:.Map)]
  syntax Map ::= K "|->" K   [klabel('_|->_), function, hook(Map:_|->_)]
  syntax priorities '_|->_ > '_Map_

  syntax Set ::= "keys" "(" Map ")"     [klabel('keys), function, hook(Map:keys)]
endmodule

module SET
  imports BOOL
  imports K

  syntax Set

  syntax Bool ::= K "in" Set            [klabel('_in_), function, hook(Set:in)]
endmodule
