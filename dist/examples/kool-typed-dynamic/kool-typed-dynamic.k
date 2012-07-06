
module KOOL-TYPED-DYNAMIC-SYNTAX

/*@ \section{Syntax}
Like for the untyped KOOL language, the syntax of typed KOOL extends
that of typed SIMPLE with object-oriented constructs. */

/*@ \subsection{Syntax from SIMPLE}
The syntax below is taken ad litteram from dynamically typed SIMPLE.
Like in untyped KOOL, we removed from the \K annotated syntax of
SIMPLE the construct for function declarations (because we want to
call them methods now) and the one for function application (because
application is not strict in the first argument anymore due to dynamic
method dispatch).  Moreover, we removed the syntax of \texttt{try-catch}
from that of SIMPLE, because we want to have typed exceptions in KOOL. */

  syntax Id ::= "main"

  syntax Type ::= "int"
                | "bool"
                | "string"
                | "void"
                | "arrayOf" Type
                    [latex("{#1}\texttt{\char91\char93}")]
                | "function" "from" Types "to" Type
                    [latex("({#1}\ \texttt{->}\ {#2})")]

  syntax Types ::= List{Type,","}      [strict]

  syntax Decl ::= "var" Exps ";"

  syntax Exp ::= Int | Bool | String | Id
               | "this"
               | "super"
               | "(" Exp ")"            [bracket]
               | "++" Exp                
               | Exp "instanceOf" Id    [strict(1)]
               | "cast" Exp "to" Id     [strict(1)]
               | "new" Id "(" Exps ")"  [strict(2)]
               | Exp "." Id      
//               | Exp ":" Type           // allowed only for declarations
               | Exp "of" Type           // allowed only for declarations
               > Exp "[" Exps "]"       [strict]
               > Exp "(" Exps ")"       [strict(2)]
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


  syntax Exps ::= List{Exp,","}

  syntax Stmt ::= "{" "}"
                | "{" Stmts "}"
                | Exp ";"                               [strict]
                | "if" Exp "then" Stmt "else" Stmt      [avoid, strict(1)]
                | "if" Exp "then" Stmt 
                | "while" Exp "do" Stmt 
                | "for" Id "=" Exp "to" Exp "do" Stmt
                | "return" Exp ";"                      [strict]
                | "return" ";"
                | "print" "(" Exps ")" ";"              [strict]
                | "throw" Exp ";"                       [strict]
                | "spawn" Stmt
                | "acquire" Exp ";"                     [strict]
                | "release" Exp ";"                     [strict]
                | "rendezvous" Exp ";"                  [strict]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts            [right]

  rule E:Exp of T:Type => '_:_(E,, T) [anywhere]
  rule 'isExp('_:_(E:Exp,, T:Type)) => true [anywhere]


  rule if E:Exp then S:Stmt => if E then S else {}
  rule (for X:Id = E1:Exp to E2:Exp do S:Stmt)
        =>
       { var '_:_(X,, int) = E1; while X <= E2 do { S X = X+1; } }

  rule var E1:Exp, E2:Exp, Es:Exps; => var (E1, .Exps); var E2, Es;

  rule var '_:_(X:Id,, T:Type) = E:Exp; => var ('_:_(X,, T), .Exps); X = E;


/*@ \subsection{KOOL Additional Syntax}
The KOOL syntactic extensions below are almost identical to their
untyped variants in untyped KOOL.  The only difference is that we add
a new type construct for class types and that now methods take typed
arguments (we achieved this the same way as in typed SIMPLE) and can
also have an explicit return type.  As a convenience to the
programmer, a macro adds an explicit type \texttt{void} whenever a
return type is not provided (e.g., one may not want to write a return
type for constructors in KOOL typed programs).  The syntax of typed
exceptions differs from that of typed SIMPLE in that the variable
bound by \texttt{catch} is now expected to be typed (we use
\textit{Exp}, but we only give semantics for the case when it has the
form \textit{Id:Type}. */

  syntax Id ::= "object"

  syntax Type ::= "class" Id

  syntax Decl ::= "method" Id "(" Exps ")" ":" Type Stmt
                | "method" Id "(" Exps ")" Stmt

  rule method X:Id (Es:Exps) S:Stmt => method X(Es) : void S

  syntax Decl ::= "class" Id "{" Stmts "}"
                | "class" Id "extends" Id "{" Stmts "}"

  rule class C:Id { Ss:Stmts } => class C extends object { Ss }

  syntax Stmt ::= "try" Stmt "catch" "(" Exp ")" Stmt 
endmodule

module KOOL-TYPED-DYNAMIC
  imports KOOL-TYPED-DYNAMIC-SYNTAX

/*@ \section{Semantics}
We first discuss the new configuration, then we include the semantics of
the constructs borrowed from SIMPLE which stay unchanged, and then we
discuss the semantics of the additional KOOL constructs and of those
from SIMPLE whose smeantics had to change. */

/*@ \subsection{Configuration}
The configuration of dynamically typed KOOL is almost identical to
that of its untyped variant.  The only difference is the cell
\textsf{return}, inside the \textsf{control} cell, whose role is to
hold the expected return type of the invoked method.  That is because
we want to dynamically check that the value that a method returns has
the expected type. */

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> ($PGM:K ~> execute) </k>
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Map </holds>
//                      <br/>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
                        <return color="LimeGreen"> void </return>
                          // holds return type
//                        <br/>
                        <crntObj color="Fuchsia"> 
                          <crntClass> object </crntClass> 
                          <envStack> .List </envStack>
                          <location multiplicity="?"> .K </location>
                        </crntObj>
                      </control>
                    </thread>
                  </threads>
//                  <br/>
                  <store color="white"> .Map </store>
                  <busy color="cyan">.Set</busy>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="brown" stream="stdout"> .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
//                  <br/>
                  <classes color="Fuchsia">
                     <class multiplicity="*" color="Fuchsia">
                        <className color="Fuchsia"> main </className>
                        <extends color="Fuchsia"> object </extends>
                        <declarations color="Fuchsia"> .K </declarations>
                     </class>
                  </classes>
                </T>

/*@ \subsection{Unchanged Semantics from SIMPLE}
The semantics below is taken over from dynamically typed SIMPLE
unchanged.  Like for untyped KOOL, the semantics of function/method
declaration and invocation, and of program initialization needs to
change.  Moreover, due to subtyping, the semantics of several imported
SIMPLE constructs can be made more general, such as that of the
return statement and of the the assignment.  Finally, since the
exceptions are now typed, they also need a different semantics.  We
removed all these from the imported semantics of SIMPLE below and gave
their typed KOOL semantics right after, together with the extended
semantics of thread spawning (which is identical to that of untyped
KOOL).  */

  syntax Val ::= Int | Bool | String
               | "arrayRef" "(" Type "," Int "," Int ")"
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

  syntax K ::= "undefined" "(" Type ")" [latex("\bot_{#1}")]

  rule <k> var ('_:_(X:Id,, T:Type), .Exps); => . ...</k>
       <env> Env:Map => Env[L:Nat/X] </env>
       <store>... . => L |-> undefined(T) ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>

  rule <k> var '_:_(X:Id[N:Int],, arrayOf T:Type); => . ...</k> 
       <env> Env:Map => Env[L/X] </env>
       <store>... . => L |-> arrayRef(arrayOf T, L +Int 1, N)
                       L +Int 1 .. L +Int N |-> undefined(T) ...</store>
       <nextLoc> L:Int => L +Int 1 +Int N </nextLoc>

  context var '_:_(X:Id[HOLE],, T:Type), .Exps ;

  syntax Id ::= "$1" | "$2"
  rule var '_:_(X:Id[N1:Int, N2:Int, Vs:Vals],, arrayOf arrayOf T:Type);
       =>
       'var_;('_:_(X[N1],, arrayOf arrayOf T));
       {
         var '_:_($1,, arrayOf arrayOf T) = X;
         for $2 = 0 to N1 - 1 do
         {
           'var_;('_:_(X[N2,Vs],, arrayOf T));
           $1[$2] = X;
         }
       }
       [structural]

  rule <k> X:Id => V:Val ...</k>
       <env>...X |-> L:Int ...</env>
       <store>... L |-> V:Val ...</store>
       [transition]

  context ++(HOLE => lvalue(HOLE))
  rule <k> ++loc(L:Int) => I:Int +Int 1 ...</k>
       <store>... L |-> (I => I +Int 1) ...</store>
       [transition]

  rule I1:Int + I2:Int => I1 +Int I2
  rule Str1:String + Str2:String => Str1 +String Str2
  rule I1:Int - I2:Int  => I1 -Int I2
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

  rule V[N1:Int, N2:Int, Vs:Vals] => V[N1][N2,Vs] [anywhere]
  rule arrayRef(_, L:Int, M:Int)[N:Int] => lookup(L +Int N)
       when N >=Int 0 andBool N <Int M
       [anywhere]

  rule sizeOf(arrayRef(_,_:Int, N:Int)) => N

  syntax Val ::= "nothing"
  rule return; => return nothing;   [structural]

  rule <k> read() => I ...</k> <in> ListItem(I) => . ...</in> [transition]

  context (HOLE => lvalue(HOLE)) = _

  rule {} => . [structural]

  rule <k> { Ss:Stmts } => Ss ~> env(Env) ...</k>
       <env> Env:Map </env>
       [structural]

  rule Ss1:Stmts Ss2:Stmts => Ss1 ~> Ss2  [structural]
  rule V:Val; => .
  rule if  true then S:Stmt else _ => S
  rule if false then _ else S:Stmt => S

  rule <k> while E:Exp do S:Stmt
       =>
       if E then {S while E do S} else {} ...</k>
       [structural]

  rule <k> print(V:Val, Vs:Vals => Vs); ...</k>
       <out>... . => ListItem(V) </out>
       when typeOf(V) ==K int orBool typeOf(V) ==K string
       [transition]

  rule print(.Vals); => . [structural]

  rule (<thread>...
           <k> .K </k>
           <holds> H:Map </holds>
        ...</thread> => .)
       <busy> Busy:Set => Busy -Set keys(H) </busy>

  rule <k> acquire V:Val; => . ...</k>
       <holds>... . => V |-> 0 ...</holds>
       <busy> Busy:Set (. => SetItem(V)) </busy>
       when notBool(V in Busy)
       [transition]

  rule <k> acquire V:Val; => . ...</k>
       <holds>...V |->( N:Int => N +Int 1)...</holds>

  rule <k> release V:Val; => . ...</k>
       <holds>... V |-> (N:Int => N -Int 1) ...</holds>
       when N >Int 0

  rule <k> release V:Val; => . ...</k>
       <holds>... V |-> 0 => . ...</holds>
       <busy>... SetItem(V)=>. ...</busy>

  rule <k> rendezvous V:Val; => . ...</k>
       <k> rendezvous V; => . ...</k>
       [transition]

// Auxiliary operations

  syntax Exp ::= "lvalue" "(" K ")"
  syntax Val ::= "loc" "(" Nat ")"

  rule <k> lvalue(X:Id) => loc(L) ...</k>
       <env>... X |-> L:Int ...</env>
       [structural]

  context lvalue(_[HOLE])
  context lvalue(HOLE[_])

  rule lvalue(lookup(L:Int)) => loc(L) [structural]

  syntax K ::= "lookup" "(" Nat ")"

  rule <k> lookup(L:Int) => V:Val ...</k>
       <store>... L |-> V ...</store>
       [transition]

  syntax K ::= "env" "(" Map ")"

  rule <k> env(Env:Map) => . ...</k>
       <env> _ => Env </env>
       [structural]
  rule (env(_) => .) ~> env(_) [structural]

// typeOf
  syntax Type ::= "typeOf" "(" K ")"   [function, klabel(typeOf)]

  rule typeOf(I:Int) => int [anywhere]              
  rule typeOf(B:Bool) => bool  [anywhere]     
  rule typeOf(_:String) => string  [anywhere] 
  rule typeOf(arrayRef(T:Type, _:Nat, _:Nat)) => T  [anywhere]
  rule typeOf(undefined(T:Type)) => T   [anywhere]
  rule typeOf(nothing) => void   [anywhere] 

  syntax Types ::= "types" "(" Exps ")"   [function, klabel(types)]

  rule types(.Exps) => void,.Types     [anywhere]
  rule types('_:_(X:Id,, T:Type), .Exps) => T,.Types  [anywhere]
  rule types('_:_(X:Id,, T:Type), (E:Exp, Es:Exps)) => T, types(E,Es)  [anywhere]

  syntax List{K} ::= Int ".." Int

  rule N1:Int..N2:Int => .List{K}
       when N1  >Int N2 
       [anywhere]

  rule N1:Int..N2:Int => N1 ,, (N1 +Int 1)..N2
       when N1 <=Int N2
       [anywhere]

/*@ \subsection{Changes to SIMPLE Semantics}
We extend/change the semantics of several SIMPLE constructs in order
to take advantage of the richer KOOL semantic infrastructure and thus
get more from the existing SIMPLE constructs. */

/*@ \subsubsection{Spawn}
Like in untyped KOOL. */

  rule <thread>...
          <k> spawn S:Stmt => . ...</k>
          <env> Env:Map </env>
          <crntObj> Obj:Bag </crntObj>
       ...</thread>
       (. => <thread>... <k> S </k>
                         <env> Env </env>
                         <crntObj> Obj </crntObj>
             ...</thread>)

/*@ \subsubsection{Assignment}
Typed KOOL allows to assign subtype instance values to supertype lvalues. */

  rule <k> loc(L:Int) = V:Val
            =>
            subtype(typeOf(V), typeOf(K)) ~> true?
            ~> unsafeCast(V, typeOf(K))
       ...</k>
       <store>... L |-> (K:K => unsafeCast(V, typeOf(K))) ...</store>
       [transition]

/*@ \subsubsection{Typed exceptions}
Exceptions are propagated now until a catch that can bind them is
encountered. */

  syntax ListItem ::= "(" Exp "," Stmt "," K "," Map "," Bag ")"
  syntax K ::= "popx"
  rule <k> (try S1:Stmt catch('_:_(X:Id,, T:Type)) S2:Stmt => S1 ~> popx) ~> K:K </k>
       <control>
         <xstack> . => ('_:_(X,, T), S2, K, Env, C) ...</xstack>
         C:Bag
       </control>
       <env> Env </env>

  rule <k> popx => . ...</k>
       <xstack> _:ListItem => . ...</xstack>

  rule <k> throw V:Val; ~> _
            =>
           if subtype(typeOf(V), T)
           then {var '_:_(X,, T) = V; S2}
           else throw V; ~> K
       </k>
       <control>
         <xstack>
            ('_:_(X:Id,, T:Type), S2:Stmt, K:K, Env:Map, C:Bag) => .
         ...</xstack>
         (_ => C)
       </control>
       <env> _ => Env </env>

/*@ \subsubsection{bindTo}
\texttt{bindto} also checks the well-formedness of the function
parameters */

  syntax K ::= "bindto" "(" Exps "," Vals ")"
  rule <k> 
         (. => X = V;) ~> bindto(('_:_(X:Id,, T:Type), XTs:Exps => XTs),
                                 (V:Val, Vs:Vals => Vs)) 
       ...</k>
       <env> Env:Map => Env[L/X] </env>
       <store>... . => L |-> undefined(T) ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>

  rule <k> bindto(.Exps, .Vals) => . ...</k>  [structural]


/*@ \subsection{Object and method closures}
The only change to untyped KOOL's values is that closures are now typed
(their last argument holds their type). */

 syntax Val ::= "objectClosure" "(" Bag ")"
              | "methodClosure" "(" Id "," Nat "," Exps "," Stmt "," Type ")"

/*@ \subsection{Class declaration}       
Like in untyped KOOL. */

  rule <k> class Class1:Id extends Class2:Id { Ss:Stmts } => . ...</k>
       <classes>... (. => <class>
                            <className> Class1 </className>
                            <extends> Class2 </extends>
                            <declarations> Ss </declarations>
                        </class>)
       ...</classes>
       [structural]

/*@ \subsection{Program initialization}
Like in untyped KOOL. */

  syntax K ::= "execute"
  rule <k> execute => new main(.Exps); </k>
       <env> . </env>
       [structural]

/*@ \subsection{Method declaration}
Methods are now typed and we need to store their types in their
closures, so that their type contract can be checked at invocation
time.  The rule below is conceptually similar to that of untyped KOOL;
the only difference is the addition of the types.  */

  rule <k> method F:Id(XTs:Exps) : T:Type S:Stmt => . ...</k>
       <crntClass> Class:Id </crntClass>
       <location> OL:Int </location>
       <env> Env => Env[L/F] </env>
       <store>... 
         .  => L |-> methodClosure(Class, OL, XTs, S, 
                                   function from types(XTs) to T)
       ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>


/*@ \subsection{New}
The semantics of \texttt{new} in dynamically typed KOOL is also
similar to that in untyped KOOL, the main difference being the
management of the return types.  Indeed, when a new object is created
we also have to stack the current type in the \textsf{return} cell in
order to be recovered after the creation of the new object.  Only the
first rule below needs to be changed; the others are identical to
those in untyped KOOL. */

  rule <k> 'new_`(_`)(Class:Id,, Vs:Vals) ~> K:K
           =>
           create(Class) ~> (storeObj ~> ('_`(_`)(Class,, Vs); return this;))
       </k>
       <env> Env:Map => . </env>
       <control> C:Bag
         <crntObj> Obj:Bag
                => <crntClass> object </crntClass>
                   <envStack> ListItem(object::<env>.Map</env>) </envStack>
                   <location> L:Int </location>
         </crntObj>
         <return> T:Type => class Class </return>
         <fstack> . => ListItem((Env, K, C <return> T </return> 
                                           <crntObj> Obj </crntObj>))
        ...</fstack>
       </control>
       <nextLoc> L:Int => L +Int 1 </nextLoc>

  syntax K ::= "create" "(" K ")"

  rule <k> create(Class:Id)
           => create(Class1) ~> setCrntClass(Class) ~> Ss ~> addEnvLayer 
       ...</k>
       <className> Class </className>
       <extends> Class1:Id </extends>
       <declarations> Ss:Stmts </declarations>
       [structural]
 
  rule <k> create(object) => . ...</k>    [structural]

  syntax K ::= "setCrntClass" "(" Id ")" 

  rule <k> setCrntClass(Class) => . ...</k>
       <crntClass> _ => Class </crntClass>
       [structural]

  syntax K ::= "addEnvLayer"

  rule <k> addEnvLayer => . ...</k>
       <env> Env:Map => . </env>
       <crntClass> Class:Id </crntClass>
       <envStack> . => ListItem(Class :: <env> Env </env>) ...</envStack> 
       [structural]

  syntax K ::= "storeObj"

  rule <k> storeObj => . ...</k>
       <crntObj> Obj:Bag (<location> L:Int </location> => .) </crntObj>
       <store>... . => L |-> objectClosure(Obj) ...</store>

/*@ \subsection{Self reference}
Like in untyped KOOL. */

  rule <k> this => objectClosure(Obj) ...</k>
       <crntObj> Obj:Bag </crntObj>

/*@ \subsection{Object member access}
Like in untyped KOOL. */

  rule <k> X:Id => '_._(this,, X) ...</k>
       <env> Env:Map </env>
       when notBool(X in keys(Env))
       [structural]

  context ('_._(HOLE,,_)) when (HOLE =/=K super)

  rule <k> '_._(objectClosure(<crntClass> Class:Id </crntClass>
                             <envStack>...
                               ListItem(Class:Id :: EnvC:BagItem)
                               EStack:List
                             </envStack>),, X:Id) 
           =>
           lookupMember(<envStack>
                          ListItem(Class :: EnvC)
                          EStack
                        </envStack>, X)
       ...</k>
       [structural]

  rule <k> '_._(super,, X:Id)
           =>
           lookupMember(<envStack> EStack </envStack>, X)
       ...</k>
       <crntClass> Class:Id </crntClass>
       <envStack>... ListItem(Class:Id :: EnvC:BagItem) EStack </envStack>
       [structural]


/*@\subsection{Method invocation}
The method lookup is the same as in untyped KOOL.
The method closure application and return are slightly different,
since we need to check that the type of the returned value is an
instance of the claimed return type of the method.  The first group of
rules below are identical to those in untyped KOOL. */

  rule <k> '_`(_`)((X:Id => V),,_) ...</k>
       <env>... X |-> L:Int ...</env>
       <store>... L |-> V:Val ...</store>

  rule <k> '_`(_`)((X:Id => '_._(this,, X)),,_) ...</k>
       <env> Env:Map </env>
    when notBool(X in keys(Env))  [structural]

  context '_`(_`)('_._(HOLE,,_),,_) when HOLE =/=K super 

  rule <k> '_`(_`)(('_._(objectClosure(Obj:Bag 
                                       <envStack>
                                         EStack:List
                                       </envStack>),, X:Id) 
                    =>
                    lookupMember(<envStack> EStack </envStack>, X)),,_)
       ...</k>
       [structural]

  rule <k> '_`(_`)(('_._(super,, X:Id) 
                    =>
                    lookupMember(<envStack> EStack </envStack>, X)),,_)
       ...</k>
       <crntClass> Class:Id </crntClass>
       <envStack>... ListItem(Class :: _) EStack:List </envStack>
    [structural]

  context '_`(_`)(HOLE,,_)
       when getKLabel HOLE ==KLabel '_`(_`) orBool
          getKLabel HOLE ==KLabel '_`[_`]

  rule <k> '_`(_`)((lookup(L) => V),,_) ...</k>
       <store>... L:Int |-> V:Val ...</store>

  syntax K ::=  "(" Map "," K "," Bag ")"

/*@ Closure application needs to also set a new return type in the
\textsf{return} cell, in order for the values returned by its body to
be checked against the return type of the method.  To do this correctly,
we also need to stack the current status of the \textsf{return} cell
and then pop it when the method returns. */

  rule <k> '_`(_`)(methodClosure(Class:Id, OL:Int, XTs:Exps, S:Stmt,
                                function from _ to T:Type),,
                  Vs:Vals) ~> K:K
           => 
           bindto(XTs,Vs) ~> S ~> return;
       </k>
       <control> C:Bag 
          <fstack> . => ListItem((Env, K, C <crntObj> Obj' </crntObj>
                                           <return> T' </return>))
          ...</fstack> 
          <crntObj> Obj':Bag => <crntClass> Class </crntClass> Obj </crntObj>
          <return> T':Type => T </return>
        </control>
       <env> Env:Map => . </env>
       <store>... 
          OL |-> objectClosure(<crntClass> _:Id </crntClass> Obj:Bag)
       ...</store>

/*@ At method return, we have to check that the type of the returned
value is a subtype of the expected return type.  Moreover, if that is
the case, then we also upcast the returned value to one of the
expected type. */

  rule <k> return V:Val; ~> _ 
            =>
            subtype(typeOf(V), T) ~> true? ~> unsafeCast(V, T) ~> K
       </k>
       <control>
         <fstack> ListItem((Env:Map, K:K, C:Bag)) => . ...</fstack>
         (<return> T:Type </return> _ => C)
       </control>
       <env> _ => Env </env>


/*@ \subsection{Instance Of}
Like in untyped KOOL. */

  rule objectClosure((_ <envStack> ListItem(Class:Id :: _) ...</envStack>))
        instanceOf Class => true

  rule objectClosure((_ <envStack>
                          ListItem(Class1:Id ::_) => .
                        ...</envStack>))
       instanceOf Class2:Id 
       when Class1 =/=K Class2
      [structural]

  rule objectClosure((_ <envStack> .List </envStack>)) instanceOf Class
       =>
       false
 
/*@ \subsection{Cast}
Unlike in untyped KOOL, in typed KOOL we actually check that the object
can indeed be cast to the claimed type. */

  rule <k> cast objectClosure((<crntClass> _:K </crntClass> Obj:Bag))
                to Class:Id 
            => objectClosure(Obj) instanceOf Class ~> true?
               ~> objectClosure(<crntClass> Class </crntClass> Obj)
       ...</k>
       [structural]

/*@ \subsection{Objects as lvalues}
Like in untyped KOOL. */

  rule <k> lvalue(X:Id => '_._(this,, X)) ...</k>
       <env> Env:Map </env>
       when notBool(X in keys(Env))
       [structural]

  context lvalue('_._(HOLE,, _:Id))

  rule <k> lvalue('_._(objectClosure(<crntClass> Class:Id </crntClass> 
                                    <envStack>...
                                       ListItem(Class :: EnvC:BagItem)
                                       EStack:List
                                    </envStack>),, X:Id)
           =>
           lookupMember(<envStack>
                          ListItem(Class :: EnvC)
                          EStack
                        </envStack>, X)) 
       ...</k>
       [structural]

/*@ \subsection{Lookup member}
Like in untyped KOOL. */

  syntax K ::= Id "::" Bag

  syntax K ::= "lookupMember" "(" BagItem "," Id ")"   
               [function, klabel(lookupMember)]

  rule lookupMember(<envStack> ListItem(_:Id :: <env>...
                                                  X:Id |-> L:Int
                                                ...</env>)
                    ...</envStack>, X)
       =>
       lookup(L) 
       [anywhere] 

  rule lookupMember(<envStack> 
                      ListItem(_:Id :: <env> Env:Map </env>) => .
                    ...</envStack>, X:Id)
       when notBool(X in keys(Env))     
       [anywhere]             

//@ \subsection{Auxilliary operations and rules}

/*@ \subsubsection{\texttt{typeOf}}
\texttt{typeOf} for the additional values. */

  rule typeOf(objectClosure(_ <envStack>
                                ListItem(Class:Id ::_)
                              ...</envStack>))
       =>
       class Class
       [anywhere]

  rule typeOf(methodClosure(_:Id, _:Nat, _, _, T:Type)) => T [anywhere]

/*@ \subsubsection{Subtyping constraints}
The subclass relation introduces a subtyping relation. */

  syntax Exp ::= "subtype" "(" Types "," Types ")"

  rule subtype(T:Type, T) => true  [structural]

  rule <k> subtype(class Class1:Id, class Class:Id)
           =>
           subtype(class Class2, class Class) 
       ...</k>
       <className> Class1 </className>
       <extends> Class2 </extends>
       when Class1 =/=K Class  [structural]

  rule subtype((T1:Type,  T2:Type,  Ts:Types),
               (T1':Type, T2':Type, Ts':Types))
       =>
       subtype(T1,T1') ~> true? ~> subtype((T2,Ts),(T2',Ts')) 
       [structural]

  rule subtype(.Types, .Types) => true  [structural]

  rule subtype(class object, class Class) => false 
       when Class =/=K object
       [structural]

/*@ \subsubsection{Unsafe Casting}
Performs unsafe casting.  One should only use it in combination with
the subtype relation above.  */

  syntax Val ::= "unsafeCast" "(" Val "," Type ")" 
                 [function, klabel(unsafeCast)]

  rule unsafeCast(objectClosure(<crntClass> _:K </crntClass> Obj:Bag), 
                  class Class:Id)
       =>
       objectClosure(<crntClass> Class </crntClass> Obj)
       [anywhere]

  rule unsafeCast(V:Val, T:Type) => V 
       when typeOf(V) ==K T 
       [anywhere]

/*@ \subsubsection{Generic guard}
A generic computational guard (should be builtin): it allows the
computation to continue only if a prefix guard evaluates to true.  */

  syntax K ::= "true?"

  rule true ~> true? => .  [structural]

endmodule
