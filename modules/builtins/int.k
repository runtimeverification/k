require bool.k
module INT-SYNTAX-HOOKS
  syntax Int ::= #Int
end module

module INT-HOOKS
  imports INT-SYNTAX-HOOKS 
  imports BOOL-HOOKS

---  declare _+Int_ : Int Int -> Int
  syntax Int ::= Int "+Int" Int 
      [function prec(33) gather(E e) latex "{#1}\mathrel{+_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_+Int_)]

---  declare _-Int_ : Int Int -> Int
  syntax Int ::= Int "-Int" Int 
      [function prec(33) gather(E e) latex "{#1}\mathrel{-_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_-Int_)]

---  declare _*Int_ : Int Int -> Int
  syntax Int ::= Int "*Int" Int 
      [function prec(31) gather(E e) latex "{#1}\mathrel{\ast_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_*Int_)]

---  declare _/Int_ : Int Int -> Int
  syntax Int ::= Int "/Int" Int 
      [function prec(31) gather(E e) latex "{#1}\mathrel{\div_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_/Int_)]

---  declare _%Int_ : Int Int -> Int
  syntax Int ::= Int "%Int" Int 
      [function prec(31) gather(E e) latex "{#1}\mathrel{\%_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_%Int_)]

---  declare _<=Int_ : Int Int -> Bool
  syntax Bool ::= Int "<=Int" Int 
      [function prec(37) gather(E e) latex "{#1}\mathrel{\leq_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_<=Int_)]

---  declare _<Int_ : Int Int -> Bool
  syntax Bool ::= Int "<Int" Int
      [function prec(37) gather(E e) latex "{#1}\mathrel{<_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_<Int_)]

---  declare _>=Int_ : Int Int -> Bool
  syntax Bool ::= Int ">=Int" Int
      [function prec(37) gather(E e) latex "{#1}\mathrel{\geq_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_>=Int_)]

---  declare _>Int_ : Int Int -> Bool
  syntax Bool ::= Int ">Int" Int
      [function prec(37) gather(E e) latex "{#1}\mathrel{>_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_>Int_)]

---  declare _==Int_ : Int Int -> Bool 
  syntax Bool ::= Int "==Int" Int         [function hook(#INT:_==Int_)]

---  declare _=/=Int_ : Int Int -> Bool
  syntax Bool ::= Int "=/=Int" Int        [function]
  define I1:Int =/=Int I2:Int => notBool(I1 ==Int I2)

  sort Nat  // ::= {I:Int | I >=Int 0}
---  declare isNat : Int -> Bool          
  syntax Bool ::= "isNat" "(" Int ")"     [function klabel(isNat)]
  define isNat(I:Int) => I >=Int 0 

---  declare _dividesInt_ : Int Int -> Bool
  syntax Bool ::= Int "dividesInt" Int    [function]
  define I1:Int dividesInt I2:Int => I2 %Int I1 ==Int 0
end module 
