module STREAM 

  syntax IExp ::=  Int
                | "hd" "(" SExp ")" [strict, context(svalue)]

//  syntax SVal ::= Int ":" SExp 

  syntax SExp ::= Id
                | "tl" "(" SExp ")" [strict, context(svalue), prefer]
                > Id "(" SExps ")"
                > IExp ":" SExp [right]
                | "[]"

  syntax Exp ::= IExp | SExp

  syntax SSpec ::= Id ":=" SExp ";"
                 | Id "(" Ids ")" ":=" SExp ";"

  syntax SPgm ::= SSpecs Exp 


  syntax SExps ::= List{SExp,","}
  syntax Ids ::= List{Id,","}
  syntax SSpecs ::= SSpec | SSpec SSpecs [right]

  syntax K ::= svalue(K) [klabel(svalue)]

  context svalue(hd(HOLE => svalue(HOLE)))

  context svalue(tl(HOLE => svalue(HOLE)))

  context svalue((HOLE => svalue(HOLE)) : _)

  configuration 
    <k> $PGM:SPgm </k>
    <sspecs> .Map </sspecs>
    <out> [] </out> 

  syntax K ::= "lambda" "(" Ids ")" SExp

  syntax KResult ::= Int

  rule isKResult(_:Int : _:SExp) => true

  rule <k> F:Id := SE:SExp; => . ...</k>
       <sspecs>... . => F |-> lambda(.Ids) SE </sspecs> 

  rule <k> F:Id(Ys:Ids) := SE:SExp; => . ...</k>
       <sspecs>... . => F |-> lambda(Ys) SE </sspecs>

  rule IE:IExp : SE':SExp => IE ~> SE' [transition]

  rule svalue(hd(I:Int : _) => I)

  rule svalue(tl(_:Int : SE:SExp) => SE)

  rule hd(I:Int : _) => I

  rule tl(_:Int : SE:SExp) => SE
  
  rule <k> I:Int => . ...</k>
       <out> SE:SExp => I : SE </out>

/* 
  - an alternative for the output (the last head value):
  rule <k> I:Int => . ...</k>
       <out> SE:SExp => I </out>
*/

  rule <k> svalue(F:Id => SE) ...</k>
       <sspecs>... F |-> lambda(.Ids) SE:SExp ...</sspecs>

  rule <k> F:Id => SE ...</k>
       <sspecs>... F |-> lambda(.Ids) SE:SExp ...</sspecs>

  rule <k> svalue(F:Id(SEs:SExps) => SE[SEs / Xs]) ...</k>
       <sspecs>... F |-> lambda(Xs:Ids) SE:SExp ...</sspecs>

  rule <k> F:Id(SEs:SExps) => SE[SEs / Xs] ...</k>
       <sspecs>... F |-> lambda(Xs:Ids) SE:SExp ...</sspecs>

  rule SS:SSpec SSs:SSpecs E:Exp => SS ~> SSs E

  rule (SS:SSpec E:Exp) => SS ~> E

  // substitution


  syntax SExp ::= SExp "[" SExps "/" Ids "]" [function]
  syntax SExp ::= SExp "<" SExp "/" Id ">" [function]
  syntax SExps ::= SExps "{" SExp "/" Id "}" [function]
  syntax IExp ::= IExp "(" SExp "/" Id ")" [function]


  rule SE:SExp[(V:SExp, (V':SExp, Vs:SExps)) / (X:Id, (X':Id, Xs:Ids))] => (SE < V / X >)[(V', Vs) / (X', Xs)]

  rule SE:SExp[(V:SExp, .SExps) / (X:Id, .Ids)] => (SE < V / X >)

  rule X:Id < V:SExp / X > => V

  rule Y:Id < V:SExp / X:Id > => Y when Y =/=K X

  rule tl(SE:SExp) < V:SExp / X:Id > =>  tl(SE < V / X >)

  rule F:Id (SEs:SExps) < V:SExp / X:Id > =>  F ( SEs { V / X } )

  rule (IE:IExp : SE:SExp) < V:SExp / X:Id > => ((IE ( V / X )) : (SE < V / X >))

  rule I:Int ( V:SExp / X:Id) => I

  rule hd(SE:SExp)(V:SExp / X:Id) => hd(SE <V / X >)

  rule (SE:SExp, (SE':SExp, SEs:SExps)){V:SExp / X:Id} => (SE < V / X >, ((SE', SEs) { V / X}))

  rule (SE:SExp, .SExps) {V:SExp / X:Id} => (SE < V / X >, .SExps)

endmodule
