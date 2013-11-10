module STREAM 

  syntax IExp ::=  Int
                | "hd" "(" SExp ")" [strict, context(svalue)]

  syntax SExp ::= Id
                | "tl" "(" SExp ")" [strict, context(svalue), prefer]
                > Id "(" SExps ")"
                > IExp ":" SExp [right]
                | "[]"

  syntax Exp ::= IExp | SExp

  syntax Eqn ::= Exp "=" Exp
  syntax Eqns ::= List{Eqn,","}

  syntax SSpec ::= Id ":=" SExp ";"
                 | Id "(" Ids ")" ":=" SExp ";"

  syntax SPgm ::= SSpecs Exp 


  syntax SExps ::= List{SExp,","}
  syntax Exps ::= List{Exp,","}
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
    <kb> .Eqns </kb> 

  syntax K ::= "lambda" "(" Ids ")" SExp

  syntax KResult ::= Int

  rule isKResult(_:Int : _:SExp) => true

  rule <k> F:Id := SE:SExp; => . ...</k>
       <sspecs>... . => F |-> lambda(.Ids) SE </sspecs>
       <kb> KB:Eqns => insert(F := SE;, KB) </kb> 

  rule <k> F:Id(Ys:Ids) := SE:SExp; => . ...</k>
       <sspecs>... . => F |-> lambda(Ys) SE </sspecs>

  rule IE:IExp : SE':SExp => IE ~> SE' // [transition]

  rule svalue(hd(I:Int : _) => I)

  rule svalue(tl(_:Int : SE:SExp) => SE)

  rule hd(I:Int : _) => I

  rule tl(_:Int : SE:SExp) => SE
  
  rule <k> I:Int => . ...</k>
       <out> SE:SExp => append(I, SE) </out>

/* 
  - an alternative for the output (the last head value):
  rule <k> I:Int => . ...</k>
       <out> SE:SExp => I </out>
*/

  rule <k> svalue(F:Id => SE) ...</k>
       <sspecs>... F |-> lambda(.Ids) SE:SExp ...</sspecs>

  rule <k> F:Id => SE ...</k>
       <sspecs>... F |-> lambda(.Ids) SE:SExp ...</sspecs>
       [transition]

  rule <k> svalue(F:Id(SEs:SExps) => simplify(SE[SEs / Xs], KB)) ...</k>
       <sspecs>... F |-> lambda(Xs:Ids) SE:SExp ...</sspecs>
       <kb> KB:Eqns </kb>

  rule <k> F:Id(SEs:SExps) => simplify(SE[SEs / Xs], KB) ...</k>
       <sspecs>... F |-> lambda(Xs:Ids) SE:SExp ...</sspecs>
       <kb> KB:Eqns </kb>
       [transition]

  rule SS:SSpec SSs:SSpecs E:Exp => SS ~> SSs E

  rule (SS:SSpec E:Exp) => SS ~> E

  // substitution

  syntax SExp ::= SExp "[" SExps "/" Ids "]" [function]
//  syntax SExp ::= SExp "<" SExp "/" Id ">" [function]
//  syntax SExps ::= SExps "{" SExp "/" Id "}" [function]
//  syntax IExp ::= IExp "(" SExp "/" Id ")" [function]


  rule SE:SExp[(V:SExp, (V':SExp, Vs:SExps)) / (X:Id, (X':Id, Xs:Ids))] => (replace(X, V, SE))[(V', Vs) / (X', Xs)]

  rule SE:SExp[(V:SExp, .SExps) / (X:Id, .Ids)] => replace(X, V, SE)

//  rule SE:SExp < V:SExp / X:Id > => replace(X, V, SE)


/*
  rule X:Id < V:SExp / X > => V

  rule Y:Id < V:SExp / X:Id > => Y when Y =/=K X

  rule tl(SE:SExp) < V:SExp / X:Id > =>  tl(SE < V / X >)

  rule F:Id (SEs:SExps) < V:SExp / X:Id > =>  F ( SEs { V / X } )

  rule (IE:IExp : SE:SExp) < V:SExp / X:Id > => ((IE ( V / X )) : (SE < V / X >))

  rule I:Int ( V:SExp / X:Id) => I

  rule hd(SE:SExp)(V:SExp / X:Id) => hd(SE <V / X >)

  rule (SE:SExp, (SE':SExp, SEs:SExps)){V:SExp / X:Id} => (SE < V / X >, ((SE', SEs) { V / X}))

  rule (SE:SExp, .SExps) {V:SExp / X:Id} => (SE < V / X >, .SExps)
*/

  // append

  syntax SExp ::= append(Int, SExp) [function]

  rule append(I:Int, []) => I : []
  rule append(I:Int, (J:Int : SE)) => J : append(I, SE)

  // simplify
  syntax SExp ::= simplify(SExp, Eqns) [function]
  rule simplify(SE:SExp, .Eqns) => SE
/*
  rule simplify(SE:SExp, (hd(F:Id) = I:Int, KB:Eqns) => simplify(SE[I/hd(F)], KB)
  rule simplify(SE:SExp, (tl(F:Id) = SE':SExp, KB:Eqns) => simplify(SE[SE'/tl(F)], KB)
*/

  rule simplify(SE:SExp, (hd(F:Id) = I:Int, KB:Eqns)) => simplify(replace(hd(F), I, SE), KB)
  rule simplify(SE:SExp, (tl(F:Id) = SE':SExp, KB:Eqns)) => simplify(replace(tl(F), SE', SE), KB)

  // replace X:K by V:K in E:K

  syntax K ::= replace(K,K,K) [function]
  syntax KList ::= replaceList(K,K,KList) [function]
  syntax KList ::= replaceListList(KList,K,KList) [function]

  rule replace(X:K, V:K, X) => V
  rule replace(XL:KLabel(XKL:KList), V:K, EL:KLabel(EKL:KList)) => EL(replaceList(XL(XKL), V, EKL))  when XL =/=KLabel EL
  rule replace(XL:KLabel(XKL:KList), V:K, XL:KLabel(EKL:KList)) => XL(replaceListList(XKL, V, EKL))

  rule replaceList(X:K, V:K, .KList) => .KList
  rule replaceList(X:K, V:K, (E:K,, EKL:KList)) => replace(X, V, E),, replaceList(X, V, EKL)

  rule replaceListList(.KList, V:K, EKL:KList) => EKL
  rule replaceListList((X:K,, XKL:KList), V:K, (E:K,, EKL:KList)) => replace(X, V, E),, replaceListList(XKL, V, EKL)

  // insert

  syntax Eqns ::= insert(SSpec, Eqns) [function]
  rule insert(F:Id := I:Int : SE:SExp;, KB:Eqns) => hd(F) = I, tl(F) = SE, KB
  rule insert(_:Id := I:IExp : _;, KB:Eqns) => KB when isInt(I) =/=K true
  rule insert(_:Id := _:Id;, KB:Eqns) => KB
  rule insert(_:Id := _:Id(_:SExps);, KB:Eqns) => KB
  rule insert(_:Id := tl(_:SExp);, KB:Eqns) => KB

endmodule
