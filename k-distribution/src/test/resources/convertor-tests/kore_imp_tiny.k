// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST
  syntax K ::= KItem
  syntax KResult
  syntax KItem ::= Id

  syntax HOLE ::= "[]"   [klabel('HOLE)]
//  syntax UserList ::= KItem "," KItem    [klabel('_,_), assoc]
//  syntax UserList ::= KItem              [klabel('.EmptyUserList)]

  syntax KSequence ::= K "~>" K   [ klabel(~>), left, assoc, unit(#EmptyK), hook(org.kframework.koreimplementation.KSequence) ]

  syntax Bool ::= "true"           [klabel('_andBool_), function, hook(#BOOL:_andBool_)]
  syntax Bool ::= "false"          [klabel('_orBool_), function, hook(#BOOL:_orBool_)]
  syntax Int ::= Token{[\-\+]? [0-9]+}     [regex("[\\+-]?\\d+"), prefer]
  syntax Id ::= Token{[A-Za-z\_][A-Za-z0-9\_]*}     [notInRules, regex("(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*")]

  syntax Bool ::= "notBool" "(" Bool ")"        [klabel('notBool_),  function, hook(#BOOL:notBool_)]
  syntax Bool ::= Bool "andBool" Bool           [klabel('_andBool_), function, hook(#BOOL:_andBool_), left]

  syntax Bool ::= K "==K" K         [klabel('_==K_),  function, hook(#K-EQUAL:_==K_), left]
  syntax Bool ::= K "=/=K" K        [klabel('_=/=K_), function, hook(#K-EQUAL:_=/=K_), left]

  syntax priority '_==K_ '_=/=K_ > 'notBool_ > '_andBool_


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

  syntax Int ::= "freshInt" "(" Int ")" [klabel('freshInt), function, freshGenerator]
//  rule 'freshInt(I:Int) => I:Int


  syntax Map ::= Map Map        [klabel('_Map_), function, hook(Map:__)]
  syntax Map ::= ".Map"         [klabel('.Map),  function, hook(Map:.Map)]
  syntax Map ::= K "|->" K      [klabel('_|->_), function, hook(Map:_|->_)]
  syntax priorities '_|->_ > '_Map_ '.Map

  syntax Set ::= "keys" "(" Map ")"     [klabel('keys), function, hook(Map:keys)]
  syntax Bool ::= K "in" Set            [klabel('_in_), function, hook(Set:in)]


  syntax KItem ::= AExp
  syntax AExp ::= Int
  syntax AExp ::= Id
  syntax AExp ::= AExp "+" AExp     [klabel('_+_), strict, left]
  syntax AExp ::= AExp "/" AExp     [klabel('_/_), strict, left]
  syntax AExp ::= "(" AExp ")"      [bracket]

  syntax KItem ::= BExp
  syntax BExp ::= Bool
  syntax BExp ::= AExp "<=" AExp        [klabel('_<=_), seqstrict]
  syntax BExp ::= "!" BExp              [klabel('!_), strict]
  syntax BExp ::= BExp "&&" BExp        [klabel('_&&_), strict(1), left]
  syntax BExp ::= "(" BExp ")"          [bracket]

  syntax Block ::= "{" "}"          [klabel('empty-block)]
  syntax Block ::= "{" Stmt "}"     [klabel('block_)]

  syntax KItem ::= Stmt
  syntax Stmt ::= Block
  syntax Stmt ::= Id "=" AExp ";"                           [klabel('_=_;), strict(2)]
  syntax Stmt ::= "if" "(" BExp ")" Block "else" Block      [klabel('if__else_), strict(1)]
  syntax Stmt ::= "while" "(" BExp ")" Block                [klabel('while__)]
  syntax Stmt ::= Stmt Stmt                                 [klabel('__), left]

  syntax KItem ::= Pgm
  syntax Pgm ::= "int" Ids ";" Stmt     [klabel('int_;_)]

  syntax KItem ::= Ids
  syntax Ids ::= List{Id, ","}

  syntax priority '_/_ > '_+_
  syntax priority '!_ > '_&&_


  syntax KItem ::= KCell
  syntax KCell ::= "<k>" K "</k>"       [klabel('<k>),       maincell]
  syntax KCell ::= "initKCell"          [klabel('initKCell), initializer]
  syntax KItem ::= StateCell
  syntax StateCell ::= "<state>" Map "</state>"     [klabel('<state>),       cell]
  syntax StateCell ::= "initStateCell"              [klabel('initStateCell), initializer]
  syntax KItem ::= TopCell
  syntax TopCell ::= "<top>" KCell StateCell "</top>"       [klabel('<top>), cell]
  syntax TopCell ::= "initTopCell"                          [initializer, klabel(initThread)]


  syntax KResult ::= Bool
  syntax KResult ::= Int
  syntax Bool ::= "isKResult" "(" KItem ")"     [klabel(isKResult), function]
  syntax Bool ::= "isInt" "(" KItem ")"     [klabel(isKResult), function]


  // AExp
  rule
    '<top>('<k>(X:Id  ~> K:K),, '<state>('_Map_('_|->_(X:Id,, I:Int),, M:Map)))
  =>
    '<top>('<k>(I:Int ~> K:K),, '<state>('_Map_('_|->_(X:Id,, I:Int),, M:Map)))

  rule
    '<top>('<k>('_+_(I1:Int,, I2:Int)    ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>('_+Int_(I1:Int,, I2:Int) ~> K:K),, SC:StateCell)
  rule
    '<top>('<k>('_/_(I1:Int,, I2:Int)    ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>('_/Int_(I1:Int,, I2:Int) ~> K:K),, SC:StateCell)
  when notBool(I2:Int ==K 0)

  // BExp
  rule
    '<top>('<k>('_<=_(I1:Int,, I2:Int)    ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>('_<=Int_(I1:Int,, I2:Int) ~> K:K),, SC:StateCell)
  rule
    '<top>('<k>('!_(B:Bool)       ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>('notBool_(B:Bool) ~> K:K),, SC:StateCell)
  rule
    '<top>('<k>('_&&_(true,, BE:BExp)    ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(BE:BExp                  ~> K:K),, SC:StateCell)
  rule
    '<top>('<k>('_&&_(false,, _:BExp)    ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(false                    ~> K:K),, SC:StateCell)

  // Block
  rule
    '<top>('<k>('empty-block(.KList) ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(.K                   ~> K:K),, SC:StateCell)
  rule
    '<top>('<k>('block_(S:Stmt) ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(S:Stmt          ~> K:K),, SC:StateCell)

  // Stmt
  rule
    '<top>('<k>('_=_;(X:Id,, I:Int)  ~> K:K),, '<state>('_Map_('_|->_(X:Id,, _:Int),, M:Map)))
  =>
    '<top>('<k>(.K                   ~> K:K),, '<state>('_Map_('_|->_(X:Id,, I:Int),, M:Map)))
  rule
    '<top>('<k>('__(S1:Stmt,, S2:Stmt) ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(S1:Stmt ~> S2:Stmt     ~> K:K),, SC:StateCell)
  rule
    '<top>('<k>('if__else_(true,,  S:Stmt,, _:Stmt) ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(S:Stmt                              ~> K:K),, SC:StateCell)
  rule
    '<top>('<k>('if__else_(false,, _:Stmt,, S:Stmt) ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(S:Stmt                         ~> K:K),, SC:StateCell)
  rule
    '<top>('<k>('while__(BE:BExp,, S:Stmt)                                                       ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>('if__else_(BE:BExp,, 'block_(S 'while__(BE:BExp,, S:Stmt)),, 'empty-block(.KList)) ~> K:K),, SC:StateCell)

  // Pgm
  rule
    '<top>('<k>('int_;_('_`,_(X:Id,, Xs:Ids),, S:Stmt) ~> K:K),, '<state>('_Map_(Rho:Map,, '.Map(.KList))))
  =>
    '<top>('<k>('int_;_(Xs:Ids,,               S:Stmt) ~> K:K),, '<state>('_Map_(Rho:Map,, '_|->_(X:Id,, 0))))
  when 'notBool_('_in_(X:Id,, 'keys(Rho:Map)))
  rule
    '<top>('<k>('int_;_(.Ids,, S:Stmt) ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(S:Stmt                 ~> K:K),, SC:StateCell)


  rule
    '<top>('<k>('if__else_(C:BExp,,  S:Stmt,, _:Stmt) ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(C ~> 'if__else_([],,  S:Stmt,, _:Stmt) ~> K:K),, SC:StateCell)
    when 'notBool_(isKResult(C))
  [heat]

  rule
      '<top>('<k>(C:KResult ~> 'if__else_([],,  S:Stmt,, _:Stmt) ~> K:K),, SC:StateCell)
    =>
      '<top>('<k>('if__else_(C,,  S:Stmt,, _:Stmt) ~> K:K),, SC:StateCell)
  [heat]

  // '_/_
  rule
    '<top>('<k>('_/_(K1:KItem,, K2:KItem)     ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(K1:KItem ~> '_/_([],,K2:KItem) ~> K:K),, SC:StateCell)
  when 'notBool_(isKResult(K1:KItem))
  [heat]
  rule
    '<top>('<k>(K1:KResult ~> '_/_([],,K2:KItem) ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>('_/_(K1:KResult,, K2:KItem)     ~> K:K),, SC:StateCell)
  when isKResult(K1)
  //[cool]
  rule
    '<top>('<k>('_/_(K1:KItem,, K2:KItem)     ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(K2:KItem ~> '_/_(K1:KItem,,[]) ~> K:K),, SC:StateCell)
  when 'notBool_(isKResult(K2:KItem))
  [heat]
  rule
    '<top>('<k>(K2:KResult ~> '_/_(K1:KItem,,[]) ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>('_/_(K1:KItem,, K2:KResult)     ~> K:K),, SC:StateCell)
  when isKResult(K2)
  //[cool]


  // '_+_
  rule
    '<top>('<k>('_+_(K1:KItem,, K2:KItem)     ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(K1:KItem ~> '_+_([],,K2:KItem) ~> K:K),, SC:StateCell)
  when 'notBool_(isKResult(K1:KItem))
  [heat]
  rule
    '<top>('<k>(K1:KResult ~> '_+_([],,K2:KItem) ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>('_+_(K1:KResult,, K2:KItem)     ~> K:K),, SC:StateCell)
  when isKResult(K1)
  //[cool]
  rule
    '<top>('<k>('_+_(K1:KItem,, K2:KItem)     ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(K2:KItem ~> '_+_(K1:KItem,,[]) ~> K:K),, SC:StateCell)
  when 'notBool_(isKResult(K2:KItem))
  [heat]
  rule
    '<top>('<k>(K2:KResult ~> '_+_(K1:KItem,,[]) ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>('_+_(K1:KItem,, K2:KResult)     ~> K:K),, SC:StateCell)
  when isKResult(K2)
  //[cool]


  // '_<=_
  rule
    '<top>('<k>('_<=_(K1:KItem,, K2:KItem)     ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(K1:KItem ~> '_<=_([],,K2:KItem) ~> K:K),, SC:StateCell)
  when 'notBool_(isKResult(K1:KItem))
  [heat]
  rule
    '<top>('<k>(K1:KResult ~> '_<=_([],,K2:KItem) ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>('_<=_(K1:KResult,, K2:KItem)     ~> K:K),, SC:StateCell)
  when isKResult(K1)
  //[cool]
  rule
    '<top>('<k>('_<=_(K1:KItem,, K2:KItem)     ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(K2:KItem ~> '_<=_(K1:KItem,,[]) ~> K:K),, SC:StateCell)
  when 'notBool_(isKResult(K2:KItem))
  [heat]
  rule
    '<top>('<k>(K2:KResult ~> '_<=_(K1:KItem,,[]) ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>('_<=_(K1:KItem,, K2:KResult)     ~> K:K),, SC:StateCell)
  when isKResult(K2)
  //[cool]

  // '_=_;
  rule
    '<top>('<k>('_=_;(V:KItem,,E) ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>(E ~> '_=_;(V,,[]) ~> K:K),, SC:StateCell)
  when 'notBool_(isKResult(E))
  [heat]
  rule
    '<top>('<k>(R:KResult ~> '_=_;(V:KItem,,[]) ~> K:K),, SC:StateCell)
  =>
    '<top>('<k>('_=_;(V,, R) ~> K:K),, SC:StateCell)
  when isKResult(R)
  //[cool]

endmodule
