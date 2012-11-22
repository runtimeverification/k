require "/modules/free-vars.k"
module TEST
  imports SUBSTITUTION
  syntax Ints ::= List{Int, ","}
  syntax Exps ::= List{Exp, ","}
  syntax Exp ::= "let" Ints  "=" Exps "in" Exp [binder, strict(2)]
             | "(" Exp ")" [bracket]
             | Int

  syntax KResult ::= Int
  
  rule isBound('let_=_in_, 1) => true
  rule isBounding('let_=_in_, 3) => true
  rule isStarBinder(let _:Ints = _:Exps in _) => true
 
  //rule isInt('#symInt(_)) => true

  syntax Variable ::= Int

  rule let (X:Int, Xs:Ints => Xs) = (B:Exp, Bs:Exps => Bs) 
        in (E:Exp => E[B/X])
  rule let .Ints = .Exps in E:Exp => E
  
  configuration
    <k>
      $PGM:K
    </k>
endmodule

