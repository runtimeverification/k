kmod X is  including PL-INT + PL-ID + K   //  every included sort (builtin) is assumed to be a KLabel
	predicate 'result(T())
	predicate 'result(I())

	context '+([],_)
	context '+(_,[])
	context '<=([],_)
	context '<=(K:K,_) if 'result(K)

  configuration <T> <k></k> <state></state> </T>
  rule <k> X:Id => I <_/k> 
       <state_> X |-> I <_/state>
  rule '+(I1:Int(), I2:Int()) => '+Int(I1(), I2())
  rule '/(I1(), I2()) => '/Int(I1, I2)  if '=/=Bool(I2(), 0())
  rule '<=(I1(), I2()) => '<=Int(I1, I2) 
  rule 'not(T:Bool()) => 'notBool(T)
  rule 'and(true(), B:K) => B:K
  rule 'and(false(), B) => false()
  rule 'skip() => .K
  rule <k> '=(X(), I()) => .K <_/k> 
       <state_> X()|->(_ => I()) <_/state>
  rule ';(S1:K, S2:K) => (S1 ~> S2)
  rule 'if(true(), S:K,_) => S
  rule 'if(false(), _, S)  => S
  rule <k> 'while(B,S) => 'if(B, ';(S, 'while(B, S)), 'skip()) <_/k>
  rule <k> 'var('list(Kl:List{K}), S) => S</k> 
       <state_> .Map => Kl |-> 0() <_/state> [structural]
   rule <k> 'var('list(Kl:List{K}), S) => S </k> 
       <state>... .Map => Kl |-> 0() ...</state> [structural]

  //  not yet defined.  any suggestions?
  // syntax Bag ::= [[ KLabel ]] [latex "\llbracket\,{#1}\,\rrbracket"] | pgm
  // macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>
  // macro pgm = [['sumPgm]]

   macro 'sumPgm() =
     'var('list('n(),'s()),
         ';('=('n(),10()),
           ';('=('s(),0()),
             'while('not('<=('n(),0())),
                   ';('=('s(),'+('s(),'n())),
                     '=('n(),'+('n(),-1())))))))
endkm
