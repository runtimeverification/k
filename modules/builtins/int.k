require bool.k
module INT-SYNTAX-HOOKS
  syntax Int ::= #Int
end module

module INT-HOOKS
  imports INT-SYNTAX-HOOKS 
  imports BOOL-HOOKS

  declare _+Int_ : Int Int -> Int
      [prec(33) gather(E e) latex "{#1}\mathrel{+_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_+Int_)]

  declare _-Int_ : Int Int -> Int
      [prec(33) gather(E e) latex "{#1}\mathrel{-_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_-Int_)]

  declare _*Int_ : Int Int -> Int
      [prec(31) gather(E e) latex "{#1}\mathrel{\ast_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_*Int_)]

  declare _/Int_ : Int Int -> Int
      [prec(31) gather(E e) latex "{#1}\mathrel{\div_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_/Int_)]

  declare _%Int_ : Int Int -> Int
      [prec(31) gather(E e) latex "{#1}\mathrel{\%_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_%Int_)]

  declare _<=Int_ : Int Int -> Bool
      [prec(37) gather(E e) latex "{#1}\mathrel{\leq_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_<=Int_)]

  declare _<Int_ : Int Int -> Bool
      [prec(37) gather(E e) latex "{#1}\mathrel{<_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_<Int_)]

  declare _>=Int_ : Int Int -> Bool
      [prec(37) gather(E e) latex "{#1}\mathrel{\geq_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_>=Int_)]

  declare _>Int_ : Int Int -> Bool
      [prec(37) gather(E e) latex "{#1}\mathrel{>_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_>Int_)]

  declare _==Int_ : Int Int -> Bool [hook(#INT:_==Int_)]

  declare _=/=Int_ : Int Int -> Bool
  define I1:Int =/=Int I2:Int => notBool(I1 ==Int I2)

  sort Nat  // ::= {I:Int | I >=Int 0}
  declare isNat : Int -> Bool
  define isNat(I:Int) => I >=Int 0 
end module 
