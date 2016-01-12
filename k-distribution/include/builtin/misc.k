// Copyright (c) 2015-2016 K Team. All Rights Reserved.

module ID
  syntax Id ::= r"(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*"     [token, autoReject]
endmodule

module ID
  imports K
  imports LOGIC

  syntax Id
  syntax Bool ::= isId ( K )         [function]
endmodule

module BOOL
  imports BASIC-K
  syntax Bool ::= "true"  [token]
  syntax Bool ::= "false" [token]

  syntax Bool ::= "notBool" Bool          [function, smtlib(not), boolOperation, latex(\neg_{\scriptstyle\it Bool}{#1}), hook(#BOOL:notBool_)]
                > Bool "andBool" Bool     [function, left, smtlib(and), boolOperation, latex({#1}\wedge_{\scriptstyle\it Bool}{#2}), hook(#BOOL:_andBool_)]
                | K "andThenBool" K       [function, left, smtlib(and), boolOperation, hook(#BOOL:_andThenBool_)]
                > Bool "xorBool" Bool     [function, left, smtlib(xor), boolOperation, hook(#BOOL:_xorBool_)]
                > Bool "orBool" Bool      [function, left, smtlib(or), boolOperation, latex({#1}\vee_{\scriptstyle\it Bool}{#2}), hook(#BOOL:_orBool_)]
                | K "orElseBool" K        [function, left, smtlib(or), boolOperation, hook(#BOOL:_orElseBool_)]
                > Bool "impliesBool" Bool [function, left, smtlib(=>), boolOperation, hook(#BOOL:_impliesBool_)]
                > left:
                  Bool "==Bool" Bool      [function, left, smtlib(=), hook(#BOOL:_==Bool_)]
                | Bool "=/=Bool" Bool     [function, left, smtlib(distinct), hook(#BOOL:_=/=Bool_)]

/*
  rule notBool true => false
  rule notBool false => true

  rule true andBool B:Bool => B:Bool
  rule B:Bool andBool true => B:Bool
  rule false andBool _:Bool => false
  rule _:Bool andBool false => false

  rule false xorBool B:Bool => B:Bool
  rule B:Bool xorBool false => B:Bool
  rule B:Bool xorBool B:Bool => false
  rule B1:Bool xorBool B2:Bool => notBool (B1 ==Bool B2)

  rule true orBool _:Bool => true
  rule _:Bool orBool true => true
  rule false orBool B:Bool => B
  rule B:Bool orBool false => B

  rule true impliesBool B:Bool => B
  rule false impliesBool _:Bool => true
  rule _:Bool impliesBool true => true
  rule B:Bool impliesBool false => notBool B

  rule B1:Bool =/=Bool B2:Bool => notBool (B1 ==Bool B2)*/
endmodule

module LOGIC
  import BOOL

  syntax KBool ::= "KTrue"                  [klabel(AND), function, hook(LOGIC:AND)]
  syntax KBool ::= "KFalse"                 [klabel(OR), function, hook(LOGIC:OR)]

  syntax KBool ::= "NOT" "(" KBool ")"  [klabel(NOT),  function, hook(LOGIC:NOT)]
  syntax KBool ::= KBool "AND" KBool    [klabel(AND), function, hook(LOGIC:AND), left]
  syntax KBool ::= KBool "OR" KBool    [klabel(OR), function, hook(LOGIC:OR), left]

  syntax LiftBoolToML ::= "^ML" "(" Bool ")" [function, hook(LOGIC:BOOL-TO-ML)]

  syntax priority 'notBool_ > '_andBool_
endmodule

module INT
  imports K
  imports LOGIC
  imports BOOL

  syntax Int ::= r"[\\+-]?[0-9]+"     [prefer, token]

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

  syntax Bool ::= "isInt" "(" K ")"     [klabel(isKResult), function]
endmodule

module K-RESULT
  import BASIC-K
  import LOGIC

  syntax KResult
  syntax Bool ::= isKResult(K) [function,klabel(isKResult)]
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

  syntax K ::= Map "[" K "]"                    [function, klabel(Map:lookup), hook(Map:lookup)]
endmodule

module SET
  imports LOGIC
  imports K

  syntax Set

  syntax Bool ::= K "in" Set            [klabel('_in_), function, hook(Set:in)]
endmodule
