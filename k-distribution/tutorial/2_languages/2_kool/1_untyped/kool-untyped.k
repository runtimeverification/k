require "domains.k"

module KOOL-UNTYPED-SYNTAX
  imports KOOL-UNTYPED-COMMON
  imports ID
endmodule

module KOOL-UNTYPED-COMMON
  imports DOMAINS-COMMON

  syntax Id ::= "Object" [token] | "Main" [token]

  syntax Decl ::= "var" Exps ";"
                | "method" Id "(" Ids ")" Block  // called "function" in SIMPLE
                | "class" Id Block               // KOOL
                | "class" Id "extends" Id Block  // KOOL

  syntax Exp ::= Int | Bool | String | Id
               | "this"                                 // KOOL
               | "super"                                // KOOL
               | "(" Exp ")"             [bracket]
               | "++" Exp
               | Exp "instanceOf" Id     [strict(1)]    // KOOL
               | "(" Id ")" Exp          [strict(2)]    // KOOL  cast
               | "new" Id "(" Exps ")"   [strict(2)]    // KOOL
               | Exp "." Id                             // KOOL
               > Exp "[" Exps "]"        [strict]
               > Exp "(" Exps ")"        [strict(2)]    // was strict in SIMPLE
               | "-" Exp                 [strict]
               | "sizeOf" "(" Exp ")"    [strict]
               | "read" "(" ")"
               > left:
                 Exp "*" Exp             [strict, left]
               | Exp "/" Exp             [strict, left]
               | Exp "%" Exp             [strict, left]
               > left:
                 Exp "+" Exp             [strict, left]
               | Exp "-" Exp             [strict, left]
               > non-assoc:
                 Exp "<" Exp             [strict, non-assoc]
               | Exp "<=" Exp            [strict, non-assoc]
               | Exp ">" Exp             [strict, non-assoc]
               | Exp ">=" Exp            [strict, non-assoc]
               | Exp "==" Exp            [strict, non-assoc]
               | Exp "!=" Exp            [strict, non-assoc]
               > "!" Exp                 [strict]
               > left:
                 Exp "&&" Exp            [strict(1), left]
               | Exp "||" Exp            [strict(1), left]
               > "spawn" Block
               > Exp "=" Exp             [strict(2), right]

  syntax Ids  ::= List{Id,","}
  syntax Exps ::= List{Exp,","}          [strict]


  syntax Block ::= "{" "}"
                | "{" Stmts "}"

  syntax Stmt ::= Decl | Block
                | Exp ";"                               [strict]
                | "if" "(" Exp ")" Block "else" Block   [avoid, strict(1)]
                | "if" "(" Exp ")" Block
                | "while" "(" Exp ")" Block
            | "for" "(" Stmts Exp ";" Exp ")" Block
                | "return" Exp ";"                      [strict]
                | "return" ";"
                | "print" "(" Exps ")" ";"              [strict]
                | "try" Block "catch" "(" Id ")" Block
                | "throw" Exp ";"                       [strict]
                | "join" Exp ";"                        [strict]
                | "acquire" Exp ";"                     [strict]
                | "release" Exp ";"                     [strict]
                | "rendezvous" Exp ";"                  [strict]

  syntax Stmts ::= Stmt
                 | Stmts Stmts                          [right]



//@ Old desugaring rules, from SIMPLE

  rule if (E) S => if (E) S else {}                                 [macro]
  rule for(Start Cond; Step) {S} => {Start while (Cond) {S Step;}}  [macro]
  rule var E1:Exp, E2:Exp, Es:Exps; => var E1; var E2, Es;          [macro]
  rule var X:Id = E; => var X; X = E;                               [macro]

//@ New desugaring rule

  rule class C:Id S => class C extends Object S                     // KOOL

endmodule

module KOOL-UNTYPED
  imports KOOL-UNTYPED-COMMON
  imports DOMAINS

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> `$PGM:Stmts ~> execute` </k>
                    //<br/>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
                      //<br/>
                        <crntObj color="Fuchsia">  // KOOL
                           <crntClass> Object </crntClass>
                           <envStack> .List </envStack>
                           <location multiplicity="?"> .K </location>
                        </crntObj>
                      </control>
                    //<br/>
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Map </holds>
                      <id color="pink"> 0 </id>
                    </thread>
                  </threads>
                //<br/>
                  <store color="white"> .Map </store>
                  <busy color="cyan">.Set </busy>
                  <terminated color="red"> .Set </terminated>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="brown" stream="stdout"> .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
                //<br/>
                  <classes color="Fuchsia">        // KOOL
                     <class multiplicity="*" color="Fuchsia">
                        <className color="Fuchsia"> Main </className>
                        <extends color="Fuchsia"> Object </extends>
                        <declarations color="Fuchsia"> .K </declarations>
                     </class>
                  </classes>
                </T>

  syntax Val ::= Int | Bool | String
               | array(Int,Int)
  syntax Vals ::= List{Val,","}
  syntax Exps ::= Vals
  syntax Exp ::= Val
  syntax KResult ::= Val

/*@ The semantics below are taken verbatim from the untyped SIMPLE
definition. */

  syntax KItem ::= "undefined"  [latex(\bot)]

  rule <k> var X:Id; => .K ...</k>
       <env> Env => Env[X <- L] </env>
       <store>... .Map => L |-> undefined ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>


  context var _:Id[HOLE];

  rule <k> var X:Id[N:Int]; => .K ...</k>
       <env> Env => Env[X <- L] </env>
       <store>... .Map => L |-> array(L +Int 1, N)
                          (L +Int 1) ... (L +Int N) |-> undefined ...</store>
       <nextLoc> L:Int => L +Int 1 +Int N </nextLoc>
    when N >=Int 0


  syntax Id ::= "$1" | "$2"
  rule var X:Id[N1:Int, N2:Int, Vs:Vals];
    => var X[N1];
       {
         var $1=X;
         for(var $2=0; $2 <= N1 - 1; ++$2) {
           var X[N2,Vs];
           $1[$2] = X;
         }
       }
    [structural]


  rule <k> X:Id => V ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V:Val ...</store>  [lookup]


  context ++(HOLE => lvalue(HOLE))
  rule <k> ++loc(L) => I +Int 1 ...</k>
       <store>... L |-> (I:Int => I +Int 1) ...</store>  [increment]


  rule I1 + I2 => I1 +Int I2
  rule Str1 + Str2 => Str1 +String Str2
  rule I1 - I2 => I1 -Int I2
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 when I2 =/=K 0
  rule I1 % I2 => I1 %Int I2 when I2 =/=K 0
  rule - I => 0 -Int I
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2

  rule V1:Val == V2:Val => V1 ==K V2
  rule V1:Val != V2:Val => V1 =/=K V2
  rule ! T:Bool => notBool(T)
  rule true  && E => E
  rule false && _ => false
  rule true  || _ => true
  rule false || E => E


  rule V:Val[N1:Int, N2:Int, Vs:Vals] => V[N1][N2, Vs]
    [structural, anywhere]

  rule array(L,_)[N:Int] => lookup(L +Int N)
    [structural, anywhere]


  rule sizeOf(array(_,N)) => N


  rule <k> return(V:Val); ~> _ => V ~> K </k>
       <control>
         <fstack> ListItem((Env,K,C)) => .List ...</fstack>
         `_ => C`
       </control>
       <env> _ => Env </env>

  syntax Val ::= "nothing"
  rule return; => return nothing;   [macro]


  rule <k> read() => I ...</k> <in> ListItem(I:Int) => .List ...</in>  [read]


  context (HOLE => lvalue(HOLE)) = _

  rule <k> loc(L) = V:Val => V ...</k> <store>... L |-> (_:Val => V) ...</store>
    [assignment]


  rule {} => .K  [structural]
  rule <k> { S } => S ~> env(Env) ...</k>  <env> Env </env>  [structural]


  rule S1::Stmts S2::Stmts => S1 ~> S2  [structural]

  rule _:Val; => .K

  rule if ( true) S else _ => S
  rule if (false) _ else S => S

  rule while (E) S => if (E) {S while(E)S}  [structural]

  rule <k> print(V:Val, Es => Es); ...</k> <out>... .List => ListItem(V) </out>
    [print]
  rule print(.Vals); => .K  [structural]


  syntax KItem ::= (Id,Stmt,K,Map,K/*ControlCellFragment*/)

  syntax KItem ::= "popx"

  rule <k> `try S1 catch(X) {S2} => S1 ~> popx` ~> K </k>
       <control>
         <xstack> .List => ListItem((X, S2, K, Env, C)) ...</xstack>
         C
       </control>
       <env> Env </env>

  rule <k> popx => .K ...</k>
       <xstack> ListItem(_) => .List ...</xstack>

  rule <k> throw V:Val; ~> _ => { var X = V; S2 } ~> K </k>
       <control>
         <xstack> ListItem((X, S2, K, Env, C)) => .List ...</xstack>
         `_ => C`
       </control>
       <env> _ => Env </env>

  rule `<thread>... <k>.K</k> <holds>H</holds> <id>T</id> ...</thread> => .Bag`
       <busy> Busy => Busy -Set keys(H) </busy>
       <terminated>... .Set => SetItem(T) ...</terminated>

  rule <k> join T:Int; => .K ...</k>
       <terminated>... SetItem(T) ...</terminated>

  rule <k> acquire V:Val; => .K ...</k>
       <holds>... .Map => V |-> 0 ...</holds>
       <busy> Busy `.Set => SetItem(V)` </busy>
    when (notBool(V in Busy:Set))  [acquire]

  rule <k> acquire V; => .K ...</k>
       <holds>... V:Val |-> (N:Int => N +Int 1) ...</holds>

  rule <k> release V:Val; => .K ...</k>
       <holds>... V |-> (N => N:Int -Int 1) ...</holds>
    when N >Int 0

  rule <k> release V; => .K ...</k> <holds>... V:Val |-> 0 => .Map ...</holds>
       <busy>... SetItem(V) => .Set ...</busy>

  rule <k> rendezvous V:Val; => .K ...</k>
       <k> rendezvous V; => .K ...</k>  [rendezvous]

//@ \subsection{Unchanged auxiliary operations from untyped SIMPLE}

  syntax Stmts ::= mkDecls(Ids,Vals)  [function]
  rule mkDecls(`X:Id, Xs:Ids`, `V:Val, Vs:Vals`) => var X=V; mkDecls(Xs,Vs)
  rule mkDecls(.Ids,.Vals) => {}

  syntax Exp ::= lookup(Int)
  rule <k> lookup(L) => V ...</k> <store>... L |-> V:Val ...</store>  [lookup]

  syntax KItem ::= env(Map)
  rule <k> env(Env) => .K ...</k>  <env> _ => Env </env>  [structural]
  rule `env(_) => .K` ~> env(_)  [structural]

  syntax Exp ::= lvalue(K)
  syntax Val ::= loc(Int)

  rule <k> lvalue(X:Id => loc(L)) ...</k> <env>... X |-> L:Int ...</env>
    [structural]

  context lvalue(_:>Exp[HOLE:>Exps])
  context lvalue(HOLE:>Exp[_:>Exps])

  rule lvalue(lookup(L:Int) => loc(L))  [structural]


  syntax Map ::= Int "..." Int "|->" K
    [function, latex({#1}\ldots{#2}\mapsto{#3})]
  rule N...M |-> _ => .Map  when N >Int M
  rule N...M |-> K:K => N |-> K (N +Int 1)...M |-> K  when N <=Int M


  syntax KItem ::= "execute"
  rule <k> execute => new Main(.Exps); </k> <env> .Map </env>  [structural]

  syntax Val ::= objectClosure(K/*CrntObjCellFragment*/)
               | methodClosure(Id,Int,Ids,Stmt)

  syntax KItem ::= (Map,K,K/*ControlCellFragment*/)

  rule <k> methodClosure(Class,OL,Xs,S)(Vs:Vals) ~> K
           => mkDecls(Xs,Vs) S return; </k>
       <env> Env => .Map </env>
       <store>... OL |-> objectClosure(<crntClass>_</crntClass> Obj)...</store>
     //<br/>
       <control>
          C
          <fstack> .List => ListItem((Env, K, C <crntObj> Obj' </crntObj>))
          ...</fstack>
          <crntObj> Obj' => <crntClass> Class </crntClass> Obj </crntObj>
       </control>


  rule <thread>...
         <k> spawn S => !T:Int ...</k>
         <env> Env </env>
         <crntObj> Obj </crntObj>
       ...</thread>
       `.Bag => <thread>...
               <k> S </k>
               <env> Env </env>
               <id> !T </id>
               <crntObj> Obj </crntObj>
             ...</thread>`


  rule <k> class Class1 extends Class2 { S } => .K ...</k>
       <classes>... `.Bag => <class>
                            <className> Class1 </className>
                            <extends> Class2 </extends>
                            <declarations> S </declarations>
                        </class>`
       ...</classes>  [structural]

  rule <k> method F:Id(Xs:Ids) S => .K ...</k>
       <crntClass> Class:Id </crntClass>
       <location> OL:Int </location>
       <env> Env => Env[F <- L] </env>
       <store>... .Map => L |-> methodClosure(Class,OL,Xs,S) ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>


  syntax KItem ::= (Id,Cell) // TODO: used to be ListItem; explain this

  rule <k> new Class:Id(Vs:Vals) ~> K
           => create(Class) ~> storeObj ~> `Class(Vs); return this;` </k>
       <env> Env => .Map </env>
       <nextLoc> L:Int => L +Int 1 </nextLoc>
     //<br/>
       <control> C
         <crntObj> Obj
                   => <crntClass> Object </crntClass>
                      <envStack> ListItem((Object, <env>.Map</env>)) </envStack>
                      <location> L </location>
         </crntObj>
         <fstack> .List => ListItem((Env, K, C <crntObj> Obj </crntObj>)) ...</fstack>
       </control>

  syntax KItem ::= create(Id)

  rule <k> create(Class:Id)
           => create(Class1) ~> setCrntClass(Class) ~> S ~> addEnvLayer ...</k>
       <className> Class </className>
       <extends> Class1:Id </extends>
       <declarations> S </declarations>  [structural]

  rule <k> create(Object) => .K ...</k>  [structural]

  syntax KItem ::= setCrntClass(Id)

  rule <k> setCrntClass(C) => .K ...</k>
       <crntClass> _ => C </crntClass>  [structural]

  syntax KItem ::= "addEnvLayer"

  rule <k> addEnvLayer => .K ...</k>
       <env> Env => .Map </env>
       <crntClass> Class:Id </crntClass>
       <envStack> .List => ListItem((Class, <env>Env</env>)) ...</envStack>
    [structural]

  syntax KItem ::= "storeObj"

  rule <k> storeObj => .K ...</k>
       <crntObj> Obj `<location> L:Int </location> => .Bag` </crntObj>
       <store>... .Map => L |-> objectClosure(Obj) ...</store>


/*@ \subsubsection{Self reference}

The semantics of \texttt{this} is straightforward: evaluate to the
current object. */

  rule <k> this => objectClosure(Obj) ...</k>
       <crntObj> Obj </crntObj>


  rule <k> X:Id => this . X ...</k> <env> Env:Map </env>
    when notBool(X in keys(Env))  [structural]

  context HOLE._::Id when (HOLE =/=K super)

  rule objectClosure(<crntClass> Class:Id </crntClass>
                     <envStack> ListItem((Class,EnvC:Cell)) EStack </envStack>)
       . X:Id
    => lookupMember(<envStack> ListItem((Class,EnvC)) EStack </envStack>, X)
    [structural]
  rule objectClosure(<crntClass> Class:Id </crntClass>
                     <envStack> ListItem((Class':Id,_)) => .List ...</envStack>)
       . X:Id
    when Class =/=K Class'  [structural]

/*  rule <k> super . X => lookupMember(<envStack>EStack</envStack>, X) ...</k>
       <crntClass> Class </crntClass>
       <envStack>... (Class,EnvC) EStack </envStack>
    [structural]*/
  rule <k> super . X => lookupMember(<envStack>EStack</envStack>, X) ...</k>
       <crntClass> Class:Id </crntClass>
       <envStack> ListItem((Class,_)) EStack </envStack>
    [structural]
  rule <k> super . X ...</k>
       <crntClass> Class </crntClass>
       <envStack> ListItem((Class':Id,_)) => .List ...</envStack>
    when Class =/=K Class'  [structural]

  rule <k> (X:Id => V)(_:Exps) ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V:Val ...</store>  [lookup]

  rule <k> (X:Id => this . X)(_:Exps) ...</k>
       <env> Env </env>
    when notBool(X in keys(Env))  [structural]

  context HOLE._::Id(_) when HOLE =/=K super

  rule (objectClosure(Obj <envStack> EStack </envStack>) . X
    => lookupMember(<envStack> EStack </envStack>, X:Id))(_:Exps)  [structural]

/*  rule <k> (super . X
            => lookupMember(<envStack>EStack</envStack>,X))(_:Exps)...</k>
       <crntClass> Class </crntClass>
       <envStack>... (Class,_) EStack </envStack>
    [structural]*/
  rule <k> (super . X
            => lookupMember(<envStack>EStack</envStack>,X))(_:Exps)...</k>
       <crntClass> Class </crntClass>
       <envStack> ListItem((Class,_)) EStack </envStack>
    [structural]
  rule <k> (super . X)(_:Exps) ...</k>
       <crntClass> Class </crntClass>
       <envStack> ListItem((Class':Id,_)) => .List ...</envStack>
    when Class =/=K Class'  [structural]

  context HOLE:Exp(_:Exps)
    when getKLabel(HOLE) ==K #klabel(`'_(_)`) orBool getKLabel(HOLE) ==K #klabel(`'_[_]`)

  rule <k> (lookup(L) => V)(_:Exps) ...</k>  <store>... L |-> V:Val ...</store>
    [lookup]

  rule objectClosure(<envStack> ListItem((C,_)) ...</envStack> _)
       instanceOf C => true

  rule objectClosure(<envStack> ListItem((C::Id,_)) => .List ...</envStack> _)
       instanceOf C'  when C =/=K C'  [structural]
//TODO: remove the sort cast ::Id of C above, when sort inference bug fixed

  rule objectClosure(<envStack> .List </envStack> _) instanceOf _ => false


  rule (C) objectClosure(<crntClass> _ </crntClass> Obj)
    => objectClosure(<crntClass> C </crntClass> Obj)


  rule <k> lvalue(X:Id => this . X) ...</k>  <env> Env </env>
    when notBool(X in keys(Env))  [structural]

  context lvalue((HOLE . _)<:Exp)

/*  rule lvalue(objectClosure(<crntClass> C </crntClass>
                            <envStack>... (C,EnvC) EStack </envStack>)
              . X
              => lookupMember(<envStack> (C,EnvC) EStack </envStack>,
                              X))  [structural]*/
  rule lvalue(objectClosure(<crntClass> Class </crntClass>
                            <envStack> ListItem((Class,EnvC:Cell)) EStack </envStack>)
              . X
              => lookupMember(<envStack> ListItem((Class,EnvC)) EStack </envStack>,
                              X))  [structural]
  rule lvalue(objectClosure(<crntClass> Class </crntClass>
                            <envStack> ListItem((Class':Id,_)) => .List ...</envStack>)
              . X)
    when Class =/=K Class'  [structural]


/*@ \subsubsection{Lookup member}

It searches for the given member in the given environment stack,
starting with the most concrete class and going up in the hierarchy. */

  syntax Exp ::= lookupMember(Cell,Id)  [function]

//  rule lookupMember(<envStack> (_, <env>... X|->L ...</env>) ...</envStack>, X)
//    => lookup(L)
  rule lookupMember(<envStack> ListItem((_, <env>... X|->L ...</env>)) ...</envStack>, X)
    => lookup(L)

//  rule lookupMember(<envStack> (_, <env> Env </env>) => .List ...</envStack>, X)
//    when notBool(X in keys(Env))
  rule lookupMember(<envStack> ListItem((_, <env> Env </env>)) Rest </envStack>, X) =>
       lookupMember(<envStack> Rest </envStack>, X)
    when notBool(X in keys(Env))
//TODO: beautify the above

endmodule
