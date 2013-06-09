module ALG-SYNTAX
 
  syntax Val ::=  Bool | Int | Float | String

  syntax Name ::= Id | Id "::" Id 

  syntax Exp ::= Val | Name
               | "(" Exp ")"  [bracket]
               | Name "(" Exps ")" [strict(1)]
               |  Name "[" Exp "]" [strict]
               > right:
                 Exp "." Exp [right]
               > "-" Exp [strict]
               > left:
                 Exp "*" Exp [left, strict]
               | Exp "/" Exp [left, strict]
               | Exp "%" Exp [left,strict]
               > left:
                 Exp "+" Exp [left, strict]
               | Exp "-" Exp [left, strict]
               > left:
                 Exp "<" Exp [left, strict]
               | Exp "<=" Exp [left, strict]
               | Exp ">" Exp [left,strict]
               | Exp ">=" Exp [left, strict]
               | Exp "!=" Exp [left,strict]
               | Exp "==" Exp [left,strict]
               > "!" Exp [strict]
               > left:
                 Exp "&&" Exp [left, strict]
               | Exp "||" Exp [left, strict]
               | Exp "=>" Exp [left, strict]

  syntax Stmt ::= Exp "=" Exp ";" [strict(2)]
               | Exp ";" [strict]
               | "{" "}"
               | "{" Stmts "}"
               | "while" "(" Exp ")" Stmt 
               | "return" Exps ";" [strict]
               | Exp "(" Ids ")" "{" Stmts "}"
               | "if" "(" Exp ")" Stmt "else" Stmt [strict(1)]
               >
                 "if" "(" Exp ")" Stmt

  syntax Stmts ::= Stmt | Stmts Stmts [left]

  syntax Ids  ::= List{Id,  ","} [strict]
  syntax Exps  ::= List{Exp,  ","} [strict]

endmodule

module ALG 
  imports ALG-SYNTAX 


  rule if(B:Exp) St:Stmt => if(B) St else {} 

  syntax Val ::= "noVal" 
               | "lambda" "(" Ids "@" Stmts ")" 
                 [latex(\lambda\,{#1}\mathrel{\bullet}{#2})]
               | "[" Vals "]"
               | "{" Map "}"

  syntax Vals ::= List{Val,","}
  syntax KResult ::= Val

  configuration 
    <k> copyGlobalState; ~> $PGM:Stmts </k>
    <state> $ST:Map </state>
    <gstate multiplicity="?"> $GST:Map </gstate>

  syntax Stmt ::= "copyGlobalState;"

  rule <k> copyGlobalState; => . ...</k>
       <state>... . => GSt ...</state>
       <gstate>  GSt:Map </gstate>


  rule <k> .K </k>
       (<gstate> _:Map </gstate> => .)

  rule <k>  '_`(_`)`{_`}(F:Name,, Xl:Ids,, Sts:Stmts)  => .  ...</k> 
       <state>... . => (F |-> lambda(Xl @ Sts)) ...</state>
       <gstate>... . => (F |-> lambda(Xl @ Sts)) ...</gstate>
       [fun-decl, structural]


  rule I1:Int + I2:Int => I1 +Int I2 [plus,structural]

  rule I1:Int - I2:Int => I1 -Int I2 [structural]

  rule I1:Int * I2:Int => I1 *Int I2 [structural]

  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=Int 0 [structural]
 
  rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=Int 0 [structural]

  rule I1:Int < I2:Int => (I1 <Int I2) [structural]

  rule I1:Int > I2:Int => (I1 >Int I2) [structural]

  rule I1:Int <= I2:Int => (I1 <=Int I2) [structural]

  rule I1:Int == I2:Int => (I1 ==Int I2) [structural]

  rule F1:Float + F2:Float => F1 +Float F2 [plus,structural]


  rule F1:Float - F2:Float => F1 -Float F2 [structural]

  rule F1:Float * F2:Float => F1 *Float F2 [structural]

  rule F1:Float / F2:Float => F1 /Float F2 when F2 =/=Float 0.0 [structural]
 
  rule F1:Float % F2:Float => F1 %Float F2 when F2 =/=Float 0.0 [structural]

  rule F1:Float < F2:Float => (F1 <Float F2) [structural]

  rule F1:Float > F2:Float => (F1 >Float F2) [structural]

  rule F1:Float <= F2:Float => (F1 <=Float F2) [structural]

  rule F1:Float == F2:Float => (F1 ==Float F2) [structural]


  rule true && B:Exp => B [structural]

  rule false && B:Exp => false [structural]

  rule true || B:Exp => true [structural]

  rule false || B:Exp => B [structural]

  rule ! false  => true [structural]

  rule ! true => false [structural]


  rule S1:String + S2:String => S1 +String S2 [structural]


  rule <k> X:Name => V ...</k>
       <state>... X |-> V:Val ...</state>
       [lookup]

  rule <k> X:Name = V:Val; => .  ...</k>
       <state> ST => ST[V / X] </state>
       [update]


  rule while(B:Exp) St:Stmt => if (B) {St while(B) St} else {}
       [while, structural]

  rule if(false) _ else St:Stmt => St [if-false]
  rule if(true) St:Stmt else _ => St [if-true]



  rule { Sts:Stmts } => Sts
       [block, structural]

  rule {} => .  [block-empty, structural]

  rule (Sts:Stmts Sts':Stmts) => (Sts ~> Sts')
       [seq-comp, structural] 


  //@ Arrays

  context '_._(_:Name[HOLE],, _:Exp)
  context '_._(_:Exp,, _:Name[HOLE])
  context '_._(_:Exp,, '_._(_:Name[HOLE],, _:Exp))

  context _:Name[HOLE] = _:Exp;
  context '_._(_:Exp,, _:Name[HOLE]) = _:Exp;
  context '_._(_:Exp,, '_._(_:Name[HOLE],, _:Exp)) = _:Exp;


  // lookup
  rule '_`[_`]({_ I |-> V:Val _},, I:Int) => V

  // update
  rule <k> X:Name[I:Int] = V:Val ; => . ...</k>
       <state>... X |-> (Vx:Val => update(Vx, I, V)) ...</state>


  // structure fields

  context '_._(HOLE,, E:Exp) when isFieldName(E)

  // lookup
  rule '_._(V:Val,, E:Exp) => lookup(V, E) when isFieldName(E)

  // update
  rule <k> '_._(X:Name,, E:Exp) = V:Val ; => . ...</k>
       <state>... X |-> (Vx:Val => update(Vx, E, V)) ...</state>
       when isFieldName(E)



  // method call

  syntax #Id ::= "self"

  syntax K ::= "updateSelf" "(" Id "," Exp ")" [strict(2)]


  rule <k> ('_._(L:Id,, F:Name (El:Exps)))
           =>
           evaluate (L, El) to .Vals following (self, Xl)::Ids; ~> updateSelf(L, self) ~>
           '_`(_`)(lambda(Xl:Ids @ Sts:Stmts),, HOLE)
       ...</k>
       <state>... F |-> lambda(Xl:Ids @ Sts:Stmts) ...</state>
       [meth-call]

  rule <k> ('_._(L:Id,, F:Id (El:Exps)))
           =>
           evaluate (L, El) to .Vals following (self, Xl); ~> updateSelf(L, self) ~>
           '_`(_`)(lambda(Xl:Ids @ Sts:Stmts),, HOLE)
       ...</k>
       <state> St:Map Str:Id :: F |-> lambda(Xl:Ids @ Sts:Stmts) </state>
       when notBool (F in keys(St))
       [meth-call]

  rule <k> (Vl:Vals ~>  updateSelf(L:Id, self) ~> '_`(_`)(lambda(Xl:Ids @ Sts:Stmts),, HOLE) ~> K:K)
           => 
           (bind Vl to (self, Xl); ~> Sts ~> updateSelf(L, self) ~> restore(St, K))
       </k>
       <state> St:Map => mergeMap(GSt, St, GSt) </state>
       <gstate> GSt:Map </gstate>
       [meth-call]

  rule <k> (return V:Val;  ~> updateSelf(L, Self:Val) ~> restore(St:Map, K:K))
           =>
          (V ~> K)
       </k>
       <state> St':Map => mergeMap(St[Self/L], St'[Self/L], GSt) </state>
       <gstate> GSt:Map => mergeMap(GSt, St'[Self/L], GSt) </gstate>
       [meth-return]

  rule <k> (updateSelf(L, Self:Val) ~> restore(St:Map, K:K))
           =>
          (noVal ~> K)
       </k>
       <state> St':Map => mergeMap(St[Self/L], St'[Self/L], GSt) </state>
       <gstate> GSt:Map => mergeMap(GSt, St'[Self/L], GSt) </gstate>
       [meth-return]

  // function call
  rule <k> '_`(_`)(lambda(Xl:Ids @ Sts:Stmts),, El:Exps)
           =>
           evaluate El to .Vals following Xl; ~>
           '_`(_`)(lambda(Xl:Ids @ Sts:Stmts),, HOLE)
       ...</k> 
       [fun-call, structural]

  syntax K ::= "restore" "(" Map "," K ")" 

  rule <k> (Vl:Vals ~> '_`(_`)(lambda(Xl:Ids @ Sts:Stmts),, HOLE) ~> K:K)
           => 
           (bind Vl to Xl; ~> Sts ~> restore(St, K))
       </k>
       <state> St:Map => mergeMap(GSt, St, GSt) </state>
       <gstate> GSt:Map </gstate>
       [fun-call]


  syntax Exps ::= "evaluate" Exps "to" Vals "following" Ids ";"


  context evaluate (HOLE, _:Exps) to _:Vals following (X:Id, _:Ids);

  rule evaluate(V:Val, El:Exps => El)
       to (Vl:Vals => '_._(Vl,, pushBack(V)))
       following (FP:Id, Xl:Ids => Xl);
       [structural]
   
  rule evaluate .Exps to Vl:Vals following .Ids; => Vl [structural]

  syntax K ::= "bind" Vals "to" Ids ";"  

  // cal by value
  rule <k> bind((V:Val, Vs:Vals) => Vs)
           to((X:Id, Xl:Ids) => Xl); 
       ...</k>
       <state> St:Map => St[V/X] </state>
       [structural]

  rule bind .Vals to .Ids; => . [ structural ]

  // return
  rule <k> (return V:Val; ~> restore(St:Map, K:K)) => (V ~> K) </k>
       <state> St':Map => mergeMap(St, St', GSt) </state> 
       <gstate> GSt:Map </gstate> 
//       <gstate> GSt:Map => mergeMap(GSt, St', GSt) </gstate>   
       [return]

  rule <k> restore(St:Map, K:K) => (noVal ~> K) </k>
       <state> St':Map => mergeMap(St, St', GSt) </state>
       <gstate> GSt:Map </gstate>
//       <gstate> GSt:Map => mergeMap(GSt, St', GSt) </gstate>
       [return]

  rule noVal ; => .


  // abstract lists

  syntax #Id ::= "empty" | "topFront" | "topBack" | "select" | "insert" | "size" 
               | "popFront" | "popBack" | "pushFront" | "pushBack" | "update"

  rule isVal(empty) => true [anywhere]
  
  rule '_`(_`)(empty,, .Exps) => [.Vals]

  context '_._(HOLE,, topFront(.Vals))
  rule '_._([V:Val, Vl:Vals],, topFront(.Vals)) => V


  context '_._(HOLE,, topBack(.Vals))
  rule '_._([V:Val, .Vals],, topBack(.Vals)) => V
  rule '_._([V:Val, Vl:Vals],, topBack(.Vals))
       => 
       '_._([Vl:Vals],, topBack(.Vals))


  context '_._(HOLE,, select(_))
  context '_._(_,, select(HOLE))

  rule '_._([V:Val, Vl:Vals],, select(0)) => V
  rule '_._([V:Val, Vl:Vals],, select(I:Int))
       => 
       '_._([Vl:Vals],, select(I -Int 1))
       when I >Int 0


  context '_._(_,, insert(HOLE:Exp, _:Exp))
  context '_._(_,, insert(_:Exp, HOLE:Exp))

  rule <k> '_._(L:Name,, insert(I:Int, V:Val)); => noVal ...</k>
       <state>... L |-> [Vl => '_._(Vl,, insert(I, V))] ...</state>


  context '_._(HOLE,, size(.Vals))
  rule '_._([.Vals],, size(.Vals)) => 0
  rule '_._([V:Val, Vl:Vals],, size(.Vals))
       => 
       '_._([Vl:Vals],, size(.Vals)) + 1


  rule <k> '_._(L:Name,, popFront(.Vals)) => noVal ...</k>
       <state>... L |-> [(V:Val, Vl:Vals) => Vl] ...</state>

// trick - I must find a general solution

  rule <k> '_._(L:Name[I:Int],, popFront(.Vals)) => noVal ...</k>
       <state>... L |-> {_ I |-> [(V:Val, Vl:Vals) => Vl] _} ...</state>

  rule <k> '_._(L:Name,, popBack(.Vals)) => noVal ...</k>
       <state>... L |-> [Vl:Vals => '_._(Vl,, popBack(.Vals))] ...</state>

  context '_._(_,, pushFront(HOLE))

  rule <k> '_._(L:Name,, pushFront(V:Val)) => noVal ...</k>
       <state>... L |-> [Vl:Vals => (V, Vl)] ...</state>

  context '_._(_,, pushBack(HOLE))

  rule <k> '_._(L:Name,, pushBack(V:Val)) => noVal ...</k>
       <state>... L |-> [Vl:Vals => '_._(Vl,, pushBack(V))] ...</state>

  context '_._(_,, update(HOLE:Exp, _:Exp))
  context '_._(_,, update(_:Exp, HOLE:Exp))

  rule <k> '_._(L:Name,, update(I:Int, V:Val)) => noVal ...</k>
       <state>... L |-> [Vl => '_._(Vl,, update(I, V))] ...</state>





  // operations on Vals

  // insert
  rule '_._(Vl:Vals,, insert(0, V:Val)) => (V, Vl) [anywhere]
  rule '_._((V:Val, Vl:Vals),, insert(I:Int, V':Val))
       => 
       '_`,_(V,, '_._(Vl:Vals,, insert(I -Int 1, V')))
       when I >Int 0
      [anywhere]

  //popBack
  rule '_._((V:Val, .Vals),, popBack(.Vals)) => .Vals [anywhere]
  rule '_`,_((V:Val, Vl:Vals),, popBack(.Vals))
       => 
       '_._(V,, '_._(Vl:Vals,, popBack(.Vals)))
       [anywhere]

  // pushBack
  rule '_._(.Vals,, pushBack(X:Val)) => (X, .Vals) [anywhere]
  rule '_._((V:Val, Vl:Vals),, pushBack(X:Val))
       => 
        '_`,_(V,, '_._(Vl:Vals,, pushBack(X)))
      [anywhere]

 // update
  rule '_._((V:Val, Vl:Vals),, update(0, V':Val)) => (V', Vl) [anywhere]
  rule '_._((V:Val, Vl:Vals),, update(I:Int, V':Val))
       => 
       (V, '_._(Vl:Vals,, update(I -Int 1, V')))
       when I >Int 0
       [anywhere]


  // operations on structured values

  //lookup
  syntax Val ::= "lookup" "(" Val "," Exp ")" [function]
               | "update" "(" Val "," Exp "," Val ")" [function]

  rule lookup({_ X |-> V:Val _}, X:Name) => V

  rule lookup({_ X |-> V:Val _}, X:Name[I:Int]) => lookup(V, I)

  rule lookup({_ X |-> V:Val _}, '_._(X:Name,, E:Exp)) => lookup(V, E)

  rule lookup({_ X |-> V:Val _}, '_._(X:Name[I:Int],, E:Exp)) => lookup(lookup(V, I), E)

  rule lookup({_ I |-> V:Val _}, I:Int) => V


  //update

  rule update({ M:Map }, X:Name, V:Val) => { M[V/X] } 

  rule update({ M:Map }, I:Int, V:Val) => { M[V/I] } 

  rule update({M:Map X |-> V':Val}, '_._(X:Name,, E:Exp), V:Val)
       =>
       {M (X |-> (update(V', E, V)))}  

  rule update({M:Map X |-> V:Val}, X:Name[I:Int], V':Val) => { M (X |-> (update(V, I, V'))) }
 
 rule update({M:Map X |-> V':Val}, '_._(X:Name[I:Int],, E:Exp), V:Val)
       =>
       {M (X |-> (update(V', I, (update(lookup(V', I), E, V)))))}


  // auxiliary functions
  syntax Bool ::= "isFieldName" "(" Exp ")" [function]
  rule isFieldName(X:Name) => true
  rule isFieldName('_`[_`](_:Name,, _:Exp)) => true
  rule isFieldName('_._(_:Name,, E:Exp)) => isFieldName(E)
  rule isFieldName('_._('_`[_`](_:Name,, _:Exp),, E:Exp)) => isFieldName(E)

  // the following function is used to update the global and local states
  syntax Map ::= "mergeMap" "(" Map "," Map "," Map ")" [function]
  rule mergeMap(L:Map, _:Map, .Map) => L
  rule mergeMap((L:Map X:Name |-> V:Val), (R:Map X |-> V':Val), (J:Map X |-> _:Val))
       =>
       mergeMap((L X |-> V'), R, J)

endmodule