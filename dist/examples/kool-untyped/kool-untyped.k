module KOOL-UNTYPED-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS

  syntax Ids ::= List{Id,","} [strict, hybrid]
  syntax Exps ::=  List{Exp,","} 

  syntax Decl ::= "var" Exps ";" 
                | "method" Id "(" Ids ")" Stmt          
                | "class" Id "{" Stmts "}"
                | "class" Id "extends" Id "{" Stmts "}"

  syntax Exp ::= Int | Bool | String | Id
               | "this"
               | "super"
               | "(" Exp ")"            [bracket]
               | "++" Exp                
               | Exp "instanceOf" Id    [strict(1)]
               | "cast" Exp "to" Id     [strict(1)]
               | "new" Id "(" Exps ")"  [strict(2)]
               | Exp "." Id      
               > Exp "[" Exps "]"       [strict]
               > Exp "(" Exps ")"       [strict]
               | "-" Exp                [strict]
               | "sizeOf" "(" Exp ")"   [strict]
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
               > "not" Exp               [strict]
               > left:
                 Exp "and" Exp           [strict, left]
               | Exp "or" Exp            [strict, left]
               > Exp "=" Exp             [strict(2), right]

  syntax Stmt ::= "{" "}"
                | "{" Stmts "}"
                | Exp ";"                           [strict]
                | "if" Exp "then" Stmt "else" Stmt  [avoid, strict(1)]
                | "if" Exp "then" Stmt    
                | "while" Exp "do" Stmt    
                | "for" Id "=" Exp "to" Exp "do" Stmt
                | "return" Exp ";"                  [strict]
                | "return" ";"
                | "write" "(" Exp ")" ";"           [strict]
                | "try" Stmt "catch" "(" Id ")" Stmt
                | "throw" Exp ";"                   [strict]
                | "spawn" Stmt    
                | "acquire" Exp ";"                 [strict]
                | "release" Exp ";"                 [strict]
                | "rendezvous" Exp ";"              [strict]
                | "print" "(" Exps ")" ";"          [strict]


  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts             [right]

  // coming from macros
  rule if E:Exp then S:Stmt => if E then S else {}
  rule (for X:Id = E1 to E2 do S) => {var X=E1, .Exps; while X <= E2 do {S X = (X + 1);}}
  rule var E1:Exp, E2:Exp, Es:Exps; => var E1, .Exps; var E2, Es;
  rule var X = E, .Exps; => var X, .Exps; X = E;

  rule class Class:Id {Ss:Stmts} => class Class extends object {Ss}


  syntax #Id ::= "object"
  syntax #Id ::= "main"

endmodule


module KOOL-UNTYPED
  imports KOOL-UNTYPED-SYNTAX


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
                  <busy color="cyan">.Set </busy>
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


  syntax Val ::= Int | Bool | String
               | "arrayRef" "(" Int "," Int ")" 
  syntax Vals ::= List{Val,","}

  syntax Exp ::= Val

  syntax KResult ::= Val

  syntax K ::= "undefined"  [latex("\bot")]

  rule <k> var X:Id; => . ...</k>
       <env> Env:Map => Env[L:Int/X] </env>
       <store>... . => L|->undefined ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>

  rule <k> var X:Id[N:Int]; => . ...</k>
       <env> Env:Map => Env[L:Int/X] </env>
       <store>... . => L |-> arrayRef(L +Int 1, N)
                       L +Int 1 .. L +Int N |-> undefined
       ...</store>
       <nextLoc> L => L +Int 1 +Int N </nextLoc>

  context var X[HOLE],.Exps;

  syntax Id ::= "$1" | "$2"
  rule var X:Id[N1:Int, N2:Int, Vs:Vals]; =>
       var X[N1];
       {
         var $1 = X;
         for $2 = 0 to (N1 - 1) do
         {
           var X[N2,Vs];
           $1[$2] = X;
         }
       }
      [structural]

  rule <k> X:Id => V:Val ...</k>
       <env>... X |-> L:Int ...</env>
       <store>... L |-> V ...</store>
       [transition]

  context ++(HOLE => lvalue(HOLE))
  rule <k> ++loc(L) => I:Int +Int 1 ...</k>
       <store>... L:Int |-> (I => I +Int 1) ...</store>
       [transition]

  rule I1:Int + I2:Int => I1 +Int I2
  rule Str1:String + Str2:String => Str1 +String Str2
  rule I1:Int - I2:Int => I1 -Int I2
  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=Int 0
  rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=Int 0
  rule - I:Int => 0 -Int I
  rule I1:Int < I2:Int => I1 <Int I2
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule I1:Int > I2:Int => I1 >Int I2
  rule I1:Int >= I2:Int => I1 >=Int I2
  rule V1:Val == V2:Val => V1 ==K V2
  rule V1:Val != V2:Val => V1 =/=K V2
  rule B1:Bool and B2:Bool => B1 andBool B2
  rule B1:Bool or B2:Bool => B1 orBool B2
  rule not(B:Bool) => notBool(B)

  rule V:Val[N1:Int,N2:Int,Vs:Vals] => V[N1][N2,Vs]           [structural, anywhere]

  rule arrayRef(L:Int,_:Nat)[N:Int] => lookup(L +Int N)       [structural, anywhere]

  syntax K ::= "lookup" "(" Int ")"  [cons("K1lookupSyn")]

  rule <k> lookup(L:Int) => V:Val ...</k>
       <store>...L|->V...</store>
       [transition]

  rule sizeOf(arrayRef(_:Int,N:Int)) => N

  rule <k> return(V:Val); ~> _ => V ~> K:K </k>
       <control> <fstack> (Env:Map,K,C:Bag) => . ...</fstack> (_ => C) </control>
       <env> _ => Env </env>

  syntax Val ::= "nothing"

  rule return; => return nothing;   [structural]

  syntax K ::= "bindto" "(" Ids "," Vals ")" [cons("K1bindtoSyn")]

  rule <k> bindto((X:Id, Xs:Ids => Xs), (V:Val,Vs:Vals => Vs)) ...</k>
       <env> Env:Map => Env[L/X] </env>
       <store>... . => L |-> V ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>

  rule <k> bindto(.Ids,.Exps) => . ...</k>  [structural]

  rule <k> read() => I ...</k> <in> ListItem(I:Int) => . ...</in>    [transition]

  context (HOLE => lvalue(HOLE)) = _

  rule <k> loc(L:Int) = V:Val => V...</k>
       <store>...L|->(_=>V)...</store>
       [transition]

  rule {} => . [structural]

  rule <k> {Ss:Stmts} => Ss~>env(Env) ...</k> <env> Env:Map </env>   [structural]

  syntax K ::= "env" "(" Map ")"

  rule <k> env(Env:Map) => . ...</k> <env> _ => Env </env>  [structural]

  rule (env(_) => .) ~> env(_)  [structural]

  rule Ss1:K Ss2:K => Ss1 ~> Ss2  [structural]

  rule V:Val; => . [structural]
  rule (Vs:Vals); => . [structural]

  rule if  true then S else _ => S
  rule if false then _ else S => S

  rule <k> while E:Exp do S:Stmt
           => if E then {S while E do S} else {}
       ...</k>
       [structural]

  rule <k> print(V:Val,Vs:Vals => Vs);...</k>
       <out>... . => ListItem(V) </out>
       [transition]

  rule print(.Vals); => .   [structural]

  syntax ListItem ::= "(" Id "," Stmt "," K "," Map "," Bag ")"
  syntax K ::= "popx"

  rule <k> (try S1:Stmt catch(X:Id) S2:Stmt => S1 ~> popx) ~> K:K </k>
       <control> <xstack> . => (X,S2,K,Env,C) ...</xstack> C:Bag </control>
       <env> Env:Map </env>

  rule <k> popx => . ...</k>
       <xstack> _:ListItem => . ...</xstack>

  rule <k> throw V:Val; ~> _ => {var X=V; S2} ~> K </k>
       <control>
          <xstack> (X:Id, S2:Stmt, K:K, Env:Map, C:Bag) => . ...</xstack> 
          (_ => C)
       </control>
       <env> _ => Env </env>

  rule (<thread>... <k>.K</k> <holds> H:Map </holds> ...</thread> => .)
       <busy> Busy:Set => Busy -Set keys(H) </busy>

  rule <k> acquire V:Val; => . ...</k>
       <holds>... . => V |-> 0 ...</holds>
       <busy> Busy:Set (. => SetItem(V)) </busy>
       when notBool(V in Busy)
       [transition]

  rule <k> acquire V:Val; => . ...</k>
       <holds>...V |-> (N:Int => N +Int 1)...</holds>

  rule <k> release V; => . ...</k> <holds>...V|->(N => N -Int 1)...</holds>
    when N >Int 0

  rule <k> release V:Val; => . ...</k>
       <holds>... V |-> 0 => . ...</holds>
       <busy>... SetItem(V)=>. ...</busy>

  rule <k> rendezvous V:Val; => . ...</k>
       <k> rendezvous V; => . ...</k>
       [transition]

  syntax Exp ::= "lvalue" "(" K ")"
  syntax Val ::= "loc" "(" Nat ")"

  rule <k> lvalue(X:Id) => loc(L) ...</k>
       <env>... X |-> L:Int ...</env>
       [structural]

  context lvalue(_[HOLE])
  context lvalue(HOLE[_])

  rule <k> lvalue(lookup(L)) => loc(L) ...</k>  [structural]

  syntax List{K} ::= Nat ".." Nat

  rule N1:Int..N2:Int => .List{K}              when N1  >Int N2 [structural, anywhere]

  rule N1:Int..N2:Int => N1 ,, (N1 +Int 1)..N2 when N1 <=Int N2 [structural, anywhere]

  rule <thread>... <k> spawn S:Stmt => . ...</k>
                   <env> Env:Map </env>
                   <crntObj> Obj:Bag </crntObj>
       ...</thread>
       (. => <thread>... <k> S </k>
                         <env> Env </env>
                         <crntObj> Obj </crntObj>
             ...</thread>)


  syntax Val ::= "objectClosure" "(" Bag ")"
               | "methodClosure" "(" Id "," Nat "," Ids "," Stmt ")"


  rule <k> class Class1:Id extends Class2:Id { Ss:Stmts } => . ...</k>
       <classes>... (. => <class>
                            <className> Class1 </className>
                            <extends> Class2 </extends>
                            <declarations> Ss </declarations>
                        </class>)
       ...</classes>  [structural]

  syntax K ::= "execute" 

  rule <k> execute => new main(.Exps); </k> <env> . </env>  [structural]

  rule <k> method F:Id(Xs:Ids) S:Stmt => . ...</k>
       <crntClass> Class:Id </crntClass>
       <location> OL:Int </location>
       <env> Env:Map => Env[L/F] </env>
       <store>... . => L |-> methodClosure(Class,OL,Xs,S) ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>

  rule <k> new Class:Id(Vs:Vals) ~> K
        => create(Class) ~> storeObj ~> Class(Vs); return this; </k>
       <env> Env:Map => . </env>
       <control> C:Bag
         <crntObj> Obj:Bag
                   =>
                   <crntClass> object </crntClass>
                   <envStack> ListItem(object::<env>.Map</env>) </envStack>
                   <location> L </location>
         </crntObj>
         <fstack> . => (Env, K, C <crntObj> Obj </crntObj>) ...</fstack>
       </control>
       <nextLoc> L:Int => L +Int 1 </nextLoc>


  syntax K ::= "create" "(" K ")"

  rule <k> create(Class:Id)
           =>
           create(Class1) ~> setCrntClass(Class) ~> Ss ~> addEnvLayer
       ...</k>
       <className> Class </className>
       <extends> Class1:Id </extends>
       <declarations> Ss:Stmts </declarations>
       [structural]

  rule <k> create(object) => . ...</k>    [structural]


  syntax K ::= "setCrntClass" "(" Id ")"

  rule <k> setCrntClass(Class:Id) => . ...</k>
       <crntClass> _ => Class </crntClass>
       [structural]


  syntax K ::= "addEnvLayer"

  rule <k> addEnvLayer => . ...</k>
       <env> Env:Map => . </env>
       <crntClass> Class:Id </crntClass>
       <envStack> . => ListItem(Class::<env>Env</env>) ...</envStack>
       [structural]

  syntax K ::= "storeObj"

  rule <k> storeObj => . ...</k>
       <crntObj> Obj:Bag (<location> L:Int </location> => .) </crntObj>
       <store>... . => L |-> objectClosure(Obj) ...</store>

  rule <k> this => objectClosure(Obj) ...</k>
       <crntObj> Obj:Bag </crntObj>

  rule <k> X:Id => '_._(this,, X) ...</k> <env> Env </env>
       when notBool(X in keys(Env))
       [structural]

  context ('_._(HOLE,,_)) when (HOLE =/=K super)

  rule <k> '_._(objectClosure(<crntClass> Class:Id </crntClass>
                   <envStack>...ListItem(Class :: EnvC:BagItem) EStack:List </envStack>),, X:Id)
           =>
           lookupMember(<envStack>ListItem(Class :: EnvC) EStack</envStack>, X)
       ...</k>
       [structural]

  rule <k> '_._(super,, X:Id) => lookupMember(<envStack>EStack</envStack>, X)...</k>
       <crntClass> Class:Id </crntClass>
       <envStack>... ListItem(Class :: EnvC:BagItem) EStack:List </envStack>
       [structural]


  rule <k> (X:Id => V)(_:Exps) ...</k>
       <env>... X |-> L:Int ...</env>
       <store>... L |-> V:Val ...</env>

  rule <k> (X:Id => '_._(this,, X))(_:Exps) ...</k>
       <env> Env </env>
    when notBool(X in keys(Env))
   [structural]


  context '_`(_`)('_._(HOLE,,_),,_) when HOLE =/=K super

  rule <k> '_`(_`)(('_._(objectClosure(Obj <envStack> EStack </envStack>),,X)
                    =>
                    lookupMember(<envStack> EStack </envStack>, X)),, _)
       ...</k>
       [structural]

  rule <k> '_`(_`)(('_._(super,,X:Id)
                     =>
                    lookupMember(<envStack> EStack </envStack>, X)),, _)
       ...</k>
       <crntClass> Class:Id </crntClass>
       <envStack>... ListItem(Class :: _) EStack:List </envStack>
       [structural]

  context '_`(_`)(HOLE,, _)
       when getKLabel HOLE ==KLabel '_`(_`) orBool
            getKLabel HOLE ==KLabel '_`[_`]


  rule <k> '_`(_`)((lookup(L:Int) => V),, _) ...</k>
       <store>... L |-> V:Val ...</store>

  syntax ListItem ::=  "(" Map "," K "," Bag ")"

  rule <k> methodClosure(Class:Id, OL:Int, Xs:Ids, S:Stmt)(Vs:Vals) ~> K:K
           =>
           bindto(Xs,Vs) ~> S ~> return;
       </k>
       <control>
          C:Bag
          <fstack> . => (Env,K,C <crntObj> Obj' </crntObj>) ...</fstack>
          <crntObj> Obj':Bag => <crntClass>Class</crntClass> Obj </crntObj>
        </control>
       <env> Env:Map => . </env>
       <store>...
           OL |-> objectClosure(<crntClass>_:Id</crntClass>Obj:Bag)
       ...</store>


  rule objectClosure(_ <envStack> ListItem(Class::_) ...</envStack>)
        instanceOf Class:Id => true

  rule objectClosure(_ <envStack> ListItem(Class1::_)
                                  =>
                                  .
                       ...</envStack>) instanceOf Class2:Id
    when Class1 =/=K Class2  [structural]

  rule objectClosure(_ <envStack> .List </envStack>) instanceOf Class:Id
       =>
       false


  rule <k> cast objectClosure(<crntClass> _:K </crntClass> Obj:Bag) to Class:Id
            =>
           objectClosure(<crntClass> Class </crntClass> Obj)
       ...</k>

  rule <k> lvalue(X:Id => '_._(this,, X)) ...</k>
       <env> Env:Map </env>
       when notBool(X in keys(Env))
       [structural]

  context lvalue('_._(HOLE,, _:Id))

  rule <k> lvalue('_._(objectClosure(<crntClass> Class:Id </crntClass>
                          <envStack>...
                             ListItem(Class :: EnvC:BagItem) EStack:List
                          </envStack>),, X)
           =>
           lookupMember(<envStack>
                           ListItem(Class :: EnvC) EStack
                        </envStack>, X))
       ...</k>  [structural]


  syntax K ::= Id "::" Bag
  // Id is the class name, BagItem is its corresponding environment

  syntax K ::= "lookupMember" "(" BagItem "," Id ")"   [function]
  // BagItem is the envStack cell, Id is the member name

// First look for the member in the top environment; if found then done.
  rule lookupMember(<envStack> ListItem(_:Id :: <env>...X:Id |-> L:Int ...</env>)
                    ...</envStack>,X)
       =>
       lookup(L)
      [structural, anywhere]

// Otherwise, recurse through the object environment stack
  rule lookupMember(<envStack> ListItem(_:Id :: <env> Env:Map </env>)
                                => .
                    ...</envStack>, X)
       when notBool(X in keys(Env))
       [structural, anywhere]



//


endmodule