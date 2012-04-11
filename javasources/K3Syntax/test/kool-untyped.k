require "built-ins.k"

module KOOL-UNTYPED-SYNTAX
  imports K

  syntax Start ::= Stmts
  syntax Ids ::= List{#Id,","} [strict, cons("Ids1ListSyn"), hybrid]
  syntax Exps ::=  List{Exp,","} [cons("Exps1ListSyn")] 

  syntax Decl ::= "var" Exps ";"

  syntax Exp ::= #Int | #Bool | #String | #Id
               | "++" Exp              [prec(0)]
               | Exp "[" Exps "]"      [strict /*prec(1)*/]
               | Exp "*" Exp           [strict /*prec(31) gather(E e)*/]
               | Exp "/" Exp           [strict /*prec(31) gather(E e)*/]
               | Exp "%" Exp           [strict /*prec(31) gather(E e)*/]
               | Exp "+" Exp           [strict /*prec(33) gather(E e)*/]
               | Exp "-" Exp           [strict /*prec(33) gather(E e)*/]
               | "-" Exp               [strict]
               | Exp "<" Exp           [strict /*prec(37)*/]
               | Exp "<=" Exp          [strict /*prec(37)*/]
               | Exp ">" Exp           [strict /*prec(37)*/]
               | Exp ">=" Exp          [strict /*prec(37)*/]
               | Exp "==" Exp          [strict /*prec(37)*/]
               | Exp "!=" Exp          [strict /*prec(37)*/]
               | Exp "=" Exp           [strict(2) /*prec(40) gather (e E)*/]
               | Exp "and" Exp         [strict /*prec(55) gather(E e)*/]
               | Exp "or" Exp          [strict /*prec(59) gather(E e)*/]
               | "not" Exp             [strict /*prec(53)*/]
               | "sizeOf" "(" Exp ")"  [strict]
               | "read" "(" ")"

  syntax Stmt ::= "{" "}"
                | "{" Stmts "}"
                | Exp ";"                               [strict /*prec(45)*/]
                | "if" Exp "then" Stmt "else" Stmt      [prefer, strict(1) /*prec(90)*/]
                | "if" Exp "then" Stmt                  /*[prec(89)]*/
                | "while" Exp "do" Stmt                 /*[prec(90)]*/
                | "for" #Id "=" Exp "to" Exp "do" Stmt  /*[prec(90)]*/
                | "return" Exp ";"                      [strict]
                | "return" ";"
                | "print" "(" Exps ")" ";"              [strict]
                | "try" Stmt "catch" "(" #Id ")" Stmt   /*[prec(90)]*/
                | "throw" Exp ";"                       [strict]
                | "spawn" Stmt                          /*[prec(90)]*/
                | "acquire" Exp ";"                     [strict]
                | "release" Exp ";"                     [strict]
                | "rendezvous" Exp ";"                  [strict]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts                      /*[prec(100) gather(e E)]*/

  syntax #Id ::= "object"

  syntax Decl ::= "method" #Id "(" Ids ")" Stmt

  syntax Decl ::= "class" #Id "{" Stmts "}"
                | "class" #Id "extends" #Id "{" Stmts "}"

  syntax Exp ::=  Exp "(" Exps ")"       [strict(2) /*prec(2)*/]

  syntax Exp ::= "new" #Id "(" Exps ")" [strict(2) /*prec(1)*/]
               | "this"
               | "super"
               | Exp "." #Id            /*[prec(1)]*/               
               | Exp "instanceOf" #Id   [strict(1) /*prec(0)*/]               
               | "cast" Exp "to" #Id    [strict(1) /*prec(0)*/]
endmodule

module KOOL-UNTYPED
  imports KOOL-UNTYPED-SYNTAX

  syntax #Id ::= "main"  

  // coming from macros
  rule if E:Exp then S:Stmt => if E then S else {}
  rule (for X:#Id = E1 to E2 do S) => {var X=E1, .Exps; while X <= E2 do {S X = (X + 1);}}
  rule var E1:Exp, E2:Exp, Es:Exps; => var E1, .Exps; var E2, Es;
  rule var X = E, .Exps; => var X, .Exps; X = E;

  rule class Class:#Id {Ss:Stmts} => class Class extends object {Ss}

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> ($PGM:K ~> execute) </k>
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Map </holds>
                      //<br/>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
// KOOL addition
                        //<br/>
                        <crntObj color="Fuchsia"> 
                           <crntClass> object </crntClass>
                           <envStack> .List </envStack>
                           <location multiplicity="?"> .K </location>
                        </crntObj>
                      </control>
                    </thread>
                  </threads>
                  //<br/>
                  <store color="white"> .Map </store>
                  <busy color="cyan">.Set</busy>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="brown" stream="stdout"> .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
// KOOL addition
                  //<br/>
                  <classes color="Fuchsia">
                     <class multiplicity="*" color="Fuchsia">
                        <className color="Fuchsia"> main </className>
                        <extends color="Fuchsia"> object </extends>
                        <declarations color="Fuchsia"> .K </declarations>
                     </class>
                  </classes>
                </T>


  syntax Val ::= #Int | #Bool | #String
               | "arrayRef" "(" #Int "," #Int ")"
  syntax Vals ::= List{Val,","}

  syntax Exp ::= Val

  syntax KResult ::= Val

  syntax K ::= "undefined"  [latex("\bot")]

  rule <k> var X:#Id; => . ...</k>
       <env> Env:Map => Env[L:#Int/X] </env>
       <store>... . => L|->undefined ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>

  rule <k> var X[N:#Int]; => . ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> arrayRef(L +Int 1, N)
                       L +Int 1 .. L +Int N |-> undefined ...</store>
       <nextLoc> L => L +Int 1 +Int N </nextLoc>

  context var X[HOLE],.Exps;

  syntax #Id ::= "$1" | "$2"
  rule var X[N1,N2,Vs:Vals]; =>
       var X[N1];
       {
         var $1 = X;
         for $2 = 0 to N1 - 1 do   // stupid parser
         {
           (var X[N2,Vs];)            // stupid parser
           $1[$2] = X;
         }
       }  [structural]

  rule <k> X => V:Val ...</k>
       <env>...X|->L...</env>
       <store>...L|->V...</store> [transition]

  context ++(HOLE => lvalue(HOLE))
  rule <k> ++loc(L) => I:#Int +Int 1 ...</k>
       <store>... L |-> (I => I +Int 1) ...</store> [transition]

  rule I1:#Int + I2:#Int => I1 +Int I2
  rule Str1:#String + Str2:#String => Str1 +String Str2
  rule I1 - I2 => I1 -Int I2
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 when I2 =/=Bool 0
  rule I1 % I2 => I1 %Int I2 when I2 =/=Bool 0
  rule - I => -Int I
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2
  rule V1:Val == V2:Val => V1 ==Bool V2
  rule V1 != V2 => V1 =/=Bool V2
  rule B1:#Bool and B2:#Bool => B1 andBool B2
  rule B1 or B2 => B1 orBool B2
  rule not(B:#Bool) => notBool(B)

  rule V[N1,N2,Vs] => V[N1][N2,Vs]           [structural, anywhere]
  rule arrayRef(L,_:#Int)[N] => lookup(L +Int N)  [structural, anywhere]
  syntax K ::= "lookup" "(" #Int ")"
  rule <k> lookup(L) => V ...</k> <store>...L|->V...</store>  [transition]

  rule sizeOf(arrayRef(_:#Int,N)) => N


  rule <k> return(V); ~> _ => V ~> K </k>
       <control> <fstack> (Env,K,C) => . ...</fstack> (_ => C) </control>
       <env> _ => Env </env>
  syntax Val ::= "nothing"
  rule return; => return nothing;   [structural]

  syntax K ::= "bindto" "(" Ids "," Vals ")"
  rule <k> bindto((X,Xs => Xs),(V,Vs:Vals => Vs)) ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> V ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>
  rule <k> bindto(.Ids,.Exps) => . ...</k>  [structural]

  rule <k> read() => I ...</k> <in> ListItem(I) => . ...</in>    [transition]

  context (HOLE => lvalue(HOLE)) = _
  rule <k> loc(L)=V => V...</k> <store>...L|->(_=>V)...</store>  [transition]

  rule {} => . [structural]
  rule <k> {Ss:Stmts} => Ss~>env(Env) ...</k> <env> Env </env>   [structural]

  syntax K ::= "env" "(" Map ")"
  rule <k> env(Env) => . ...</k> <env> _ => Env </env>  [structural]

  rule (env(_) => .) ~> env(_)  [structural]

  rule Ss1:Stmts Ss2:Stmts => Ss1 ~> Ss2  [structural]

  rule V; => .

  rule if  true then S else _ => S
  rule if false then _ else S => S

  rule <k> while E:Exp do S
    => if E then {S while E do S} else {} ...</k> [structural]

  rule <k> print(V,Vs => Vs);...</k> <out>... . => ListItem(V) </out>
    [transition]
  rule print(.Vals); => .   [structural]

  syntax ListItem ::= "(" #Id "," Stmt "," K "," Map "," Bag ")"
  syntax K ::= "popx"
  rule <k> (try S1:Stmt catch(X) S2:Stmt => S1 ~> popx) ~> K </k>
       <control> <xstack> . => (X,S2,K,Env,C) ...</xstack> C:Bag </control>
       <env> Env </env>
  rule <k> popx => . ...</k> <xstack> _:ListItem => . ...</xstack>
  rule <k> throw V; ~> _ => {var X=V; S2} ~> K </k>
       <control> <xstack> (X,S2,K,Env,C) => . ...</xstack> (_ => C) </control>
       <env> _ => Env </env>


//  rule <thread>... <k> spawn S => . ...</k> <env> Env </env> ...</thread>
//       (. => <thread>... <k> S </k> <env> Env </env> ...</thread>)
  rule (<thread>... <k>.K</k> <holds> H:Map </holds> ...</thread> => .)
       <busy> Busy:Set => Busy -Set keys(H) </busy>
  rule <k> acquire V; => . ...</k> <holds>... . => V|->0 ...</holds>
       <busy> Busy (. => SetItem(V)) </busy>
    when notBool(V in Busy) [transition]
  rule <k> acquire V; => . ...</k> <holds>...V|->(N => N +Int 1)...</holds>
  rule <k> release V; => . ...</k> <holds>...V|->(N => N -Int1)...</holds>
    when N >Int 0
  // used prefix notation for -Int because of parsing problems
  rule <k> release V; => . ...</k> <holds>... V|->0 => . ...</holds>
       <busy>... SetItem(V)=>. ...</busy>
  rule <k> rendezvous V; => . ...</k>
       <k> rendezvous V; => . ...</k>  [transition]

  syntax Exp ::= "lvalue" "(" K ")"
  syntax Val ::= "loc" "(" #Int ")"
  rule <k> lvalue(X) => loc(L:#Int) ...</k>
       <env>... X|->L ...</env>  [structural]
  context lvalue(_[HOLE])
  context lvalue(HOLE[_])
  rule <k> lvalue(lookup(L)) => loc(L) ...</k>  [structural]

  syntax List{K} ::= #Int ".." #Int
  rule N1:#Int..N2:#Int => .List{K}              when N1  >Int N2 [structural]
  rule N1:#Int..N2:#Int => N1 ,, (N1 +Int 1)..N2 when N1 <=Int N2 [structural]



  rule <thread>... <k> spawn S => . ...</k>
                   <env> Env </env>
                   <crntObj> Obj </crntObj>
       ...</thread>
       (. => <thread>... <k> S </k>
                         <env> Env </env>
                         <crntObj> Obj </crntObj>
             ...</thread>)


  syntax Val ::= "objectClosure" "(" Bag ")"
               | "methodClosure" "(" #Id "," #Int "," Ids "," Stmt ")"


  rule <k> class Class1:#Id extends Class2:#Id { Ss:Stmts } => . ...</k>
       <classes>... (. => <class>
                            <className> Class1 </className>
                            <extends> Class2 </extends>
                            <declarations> Ss </declarations>
                        </class>)
       ...</classes>  [structural]


  syntax K ::= "execute"
  rule <k> execute => new main(.Exps); </k> <env> . </env>  [structural]


  rule <k> method F:#Id(Xs:Ids) S:Stmt => . ...</k>
       <crntClass> Class:#Id </crntClass>
       <location> OL:#Int </location>
       <env> Env => Env[L/F] </env>
       <store>... . => L|->methodClosure(Class,OL,Xs,S) ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>


  rule <k> new Class(Vs) ~> K 
        => create(Class) ~> storeObj ~> Class(Vs); return this; </k>
       <env> Env => . </env>
       <control> C:Bag
         <crntObj> Obj
                => <crntClass> object </crntClass>
                   <envStack> ListItem(object::<env>.Map</env>) </envStack>
                   <location> L </location>
         </crntObj>
         <fstack> . => (Env, K, C <crntObj> Obj </crntObj>) ...</fstack>
       </control>
       <nextLoc> L => L +Int 1 </nextLoc>


  syntax K ::= "create" "(" K ")"

  rule <k> create(Class)
        => create(Class1) ~> setCrntClass(Class) ~> Ss ~> addEnvLayer ...</k>
       <className> Class </className>
       <extends> Class1 </extends>
       <declarations> Ss </declarations>  [structural]
  rule <k> create(object) => . ...</k>    [structural]


  syntax K ::= "setCrntClass" "(" #Id ")" 
  rule <k> setCrntClass(Class) => . ...</k>
       <crntClass> _ => Class </crntClass>  [structural]


  syntax K ::= "addEnvLayer"
  rule <k> addEnvLayer => . ...</k>
       <env> Env => . </env>
       <crntClass> Class </crntClass>
       <envStack> . => ListItem(Class::<env>Env</env>) ...</envStack> 
    [structural]


  syntax K ::= "storeObj"
  rule <k> storeObj => . ...</k>
       <crntObj> Obj (<location> L </location> => .) </crntObj>
       <store>... . => L |-> objectClosure(Obj) ...</store>


  rule <k> this => objectClosure(Obj) ...</k>  
       <crntObj> Obj </crntObj>



// To avoid parsing ambiguity, use _._(this,X) instead of this.X
  rule <k> X => '_._(this,,X) ...</k> <env> Env </env>
    when notBool(X in keys(Env))  [structural]

  context ('_._(HOLE,,_)) when (HOLE =/=Bool super)
  rule <k> '_._(objectClosure(<crntClass> Class </crntClass>
                   <envStack>...ListItem(Class :: EnvC) EStack </envStack>),,X)
        => lookupMember(<envStack>ListItem(Class :: EnvC) EStack</envStack>, X)
       ...</k>  [structural]

  rule <k> '_._(super,,X) => lookupMember(<envStack>EStack</envStack>, X)...</k>
       <crntClass> Class:#Id </crntClass>
       <envStack>... ListItem(Class :: EnvC) EStack </envStack>
    [structural]


  rule <k> (X => V)(_) ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V ...</env>

  rule <k> (X => this . X)(_) ...</k>
       <env> Env </env>
    when notBool(X in keys(Env))  [structural]

// We would like to write the rule above as
//   rule <k> (X => _._(this,X))(_) ...</k>
// or even
//   rule <k> (X => this.X)(_) ...</k>
// but, unfortunately, our current Maude-based parser does not allow it
// Same applies to other rules

  context '_`(_`)('_._(HOLE,,_),,_) when HOLE =/=Bool super 

  rule <k> '_`(_`)(('_._(objectClosure(Obj <envStack> EStack </envStack>),,X) 
        => lookupMember(<envStack> EStack </envStack>, X)),,_) ...</k>
    [structural]

  rule <k> '_`(_`)(('_._(super,,X) 
        => lookupMember(<envStack> EStack </envStack>, X)),,_) ...</k>
       <crntClass> Class:#Id </crntClass>
       <envStack>... ListItem(Class :: _) EStack </envStack>
    [structural]

  context '_`(_`)(HOLE,,_)
       when getKLabel HOLE ==Bool '_`(_`) orBool getKLabel HOLE ==Bool '_`[_`]


  rule <k> '_`(_`)((lookup(L) => V),,_) ...</k>
       <store>... L |-> V ...</store>

  syntax ListItem ::=  "(" Map "," K "," Bag ")"
  rule <k> '_`(_`)(methodClosure(Class,OL:#Int,Xs:Ids,S:Stmt),, Vs:Vals) ~> K:K
        => bindto(Xs,Vs) ~> S ~> return; </k>
       <control> C:Bag
          <fstack> . => (Env,K,C <crntObj> Obj' </crntObj>) ...</fstack>
          <crntObj> Obj':Bag => <crntClass>Class</crntClass> Obj </crntObj>
        </control>
       <env> Env => . </env>
       <store>... OL |-> objectClosure(<crntClass>_:#Id</crntClass>Obj:Bag) 
       ...</store>


  rule objectClosure(_ <envStack>ListItem(Class::_)...</envStack>)
        instanceOf Class => true
  rule objectClosure(_ <envStack> ListItem(Class1::_)
                      => . ...</envStack>) instanceOf Class2 
    when Class1 =/=Bool Class2  [structural]
  rule objectClosure(_ <envStack> .List </envStack>) instanceOf Class
    => false
 


  rule <k> cast objectClosure(<crntClass> _:K </crntClass> Obj) to Class
        => objectClosure(<crntClass> Class </crntClass> Obj) ...</k>



  rule <k> lvalue(X => '_._(this,,X)) ...</k> <env> Env </env>
    when notBool(X in keys(Env))  [structural]

  context lvalue('_._(HOLE,,_:#Id))
  rule <k> lvalue('_._(objectClosure(<crntClass> Class </crntClass> 
                          <envStack>...
                            ListItem(Class :: EnvC) EStack
                          </envStack>),, X)
        => lookupMember(<envStack>ListItem(Class :: EnvC:BagItem) EStack:List
                        </envStack>, X)) 
       ...</k>  [structural]
  

  syntax K ::= #Id "::" Bag
  // Id is the class name, BagItem is its corresponding environment

  syntax K ::= "lookupMember" "(" BagItem "," #Id ")" [declare]
  // BagItem is the envStack cell, Id is the member name

// First look for the member in the top environment; if found then done.
  rule lookupMember(<envStack> ListItem(_:#Id :: <env>...X|->L...</env>)
                    ...</envStack>,X) => lookup(L)  [structural]
// Otherwise, recurse through the object environment stack
  rule lookupMember(<envStack> ListItem(_:#Id :: <env> Env </env>)
                            => . ...</envStack>, X)
    when notBool(X in keys(Env))                      [structural]

endmodule
