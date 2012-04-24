require bool.k
module INT-SYNTAX-HOOKS
  syntax Int ::= #Int
end module

module INT-HOOKS
  imports INT-SYNTAX-HOOKS 
  imports BOOL-HOOKS

  syntax Int ::= Int "+Int" Int 
      [function prec(33) gather(E e) latex "{#1}\mathrel{+_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_+Int_)]

  syntax Int ::= Int "-Int" Int 
      [function prec(33) gather(E e) latex "{#1}\mathrel{-_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_-Int_)]

  syntax Int ::= Int "*Int" Int 
      [function prec(31) gather(E e) latex "{#1}\mathrel{\ast_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_*Int_)]

  syntax Int ::= Int "/Int" Int 
      [function prec(31) gather(E e) latex "{#1}\mathrel{\div_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_/Int_)]

  syntax Int ::= Int "%Int" Int 
      [function prec(31) gather(E e) latex "{#1}\mathrel{\%_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_%Int_)]

  syntax Bool ::= Int "<=Int" Int 
      [function prec(37) gather(E e) latex "{#1}\mathrel{\leq_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_<=Int_)]

  syntax Bool ::= Int "<Int" Int
      [function prec(37) gather(E e) latex "{#1}\mathrel{<_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_<Int_)]

  syntax Bool ::= Int ">=Int" Int
      [function prec(37) gather(E e) latex "{#1}\mathrel{\geq_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_>=Int_)]

  syntax Bool ::= Int ">Int" Int
      [function prec(37) gather(E e) latex "{#1}\mathrel{>_{\scriptstyle\it Int}}{#2}"
       hook(#INT:_>Int_)]

  syntax Bool ::= Int "==Int" Int         [function hook(#INT:_==Int_)]

  syntax Bool ::= Int "=/=Int" Int        [function]
  define I1:Int =/=Int I2:Int => notBool(I1 ==Int I2)

  syntax Nat ::= dummyNat // ::= {I:Int | I >=Int 0}
  syntax Bool ::= "isNat" "(" Int ")"     [function klabel(isNat)]
  define isNat(I:Int) => true // the old definition broke any custom 'isNat()s
    when I >=Int 0 

  syntax Bool ::= Int "dividesInt" Int    [function]
  define I1:Int dividesInt I2:Int => I2 %Int I1 ==Int 0
  
  syntax Bool ::= "absInt" Int [function]
  define absInt(I:Int) => I:Int
    when I:Int >=Int 0
  define absInt(I:Int) => 0 -Int I:Int
    when I:Int <Int 0
	
  syntax Bool ::= "maxInt" "(" Int "," Int ")" [function]
  define maxInt(I1:Int, I2:Int) => I1:Int
    when I1:Int >=Int I2:Int
  define maxInt(I1:Int, I2:Int) => I2:Int
    when I1:Int <Int I2:Int
  syntax Bool ::= "minInt" "(" Int "," Int ")" [function]
  define minInt(I1:Int, I2:Int) => I2:Int
    when I1:Int >=Int I2:Int
  define minInt(I1:Int, I2:Int) => I1:Int
    when I1:Int <Int I2:Int
	
  syntax Bool ::= Int "<<Int" Int [function hook(#INT:_<<Int_)]
  syntax Bool ::= Int ">>Int" Int [function hook(#INT:_>>Int_)]
  syntax Bool ::= Int "&Int" Int [function hook(#INT:_&Int_)]
  syntax Bool ::= Int "|Int" Int [function hook(#INT:_|Int_)]
  syntax Bool ::= Int "^Int" Int [function hook(#INT:_^Int_)]
  syntax Bool ::= Int "dividesInt" Int [function hook(#INT:_dividesInt_)]
  syntax Bool ::= Int "xorInt" Int [function hook(#INT:_xorInt_)]
  syntax Bool ::= "~Int" Int [function hook(#INT:~Int_)]
end module 
