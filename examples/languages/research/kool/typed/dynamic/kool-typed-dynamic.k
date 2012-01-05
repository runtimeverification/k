
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

  syntax #Id ::= "main"

  syntax Type ::= "int"
                | "bool"
                | "string"
                | "void"
                | "arrayOf" Type
                    [:prec(1) latex "{#1}\texttt{\char91\char93}":]
                | "function" "from" Types "to" Type
                    [:prec(1) latex "({#1}\ \texttt{->}\ {#2})":]
  syntax Types ::= List{Type,","}

  syntax Decl ::= "var" Exps ";"

  syntax Exp ::= #Int | #Bool | #String | #Id
               | "++" Exp              [:prec(0):]
               | Exp "+" Exp           [:strict prec(33) gather(E e):]
               | Exp "-" Exp           [:strict prec(33) gather(E e):]
               | Exp "*" Exp           [:strict prec(31) gather(E e):]
               | Exp "/" Exp           [:strict prec(31) gather(E e):]
               | Exp "%" Exp           [:strict prec(31) gather(E e):]
               | "-" Exp               [:strict:]
               | Exp "<" Exp           [:strict prec(37):]
               | Exp "<=" Exp          [:strict prec(37):]
               | Exp ">" Exp           [:strict prec(37):]
               | Exp ">=" Exp          [:strict prec(37):]
               | Exp "==" Exp          [:strict prec(37):]
               | Exp "!=" Exp          [:strict prec(37):]
               | Exp "and" Exp         [:strict prec(55) gather(E e):]
               | Exp "or" Exp          [:strict prec(59) gather(E e):]
               | "not" Exp             [:strict prec(53):]
               | Exp "[" Exps "]"      [:strict prec(1):]
               | "sizeOf" "(" Exp ")"  [:strict:]
               | "read" "(" ")"
               | Exp "=" Exp           [:strict(2) prec(40) gather (e E):]
               | Exp ":" Type          [:prec(10):]
                                       // allowed only for declarations
  syntax Exps ::= List{Exp,","}

  syntax Stmt ::= "{" "}"
                | "{" Stmts "}"
                | Exp ";"                               [:strict prec(45):]
                | "if" Exp "then" Stmt "else" Stmt      [:strict(1) prec(90):]
                | "if" Exp "then" Stmt                  [:prec(89):]
                | "while" Exp "do" Stmt                 [:prec(90):]
                | "for" #Id "=" Exp "to" Exp "do" Stmt  [:prec(90):]
                | "return" Exp ";"                      [:strict:]
                | "return" ";"
                | "print" "(" Exps ")" ";"              [:strict:]
                | "throw" Exp ";"                       [:strict:]
                | "spawn" Stmt                          [:prec(90):]
                | "acquire" Exp ";"                     [:strict:]
                | "release" Exp ";"                     [:strict:]
                | "rendezvous" Exp ";"                  [:strict:]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts            [:seqstrict prec(100) gather(e E):]

  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X = E1 to E2 do S) = {var X:int=E1; while X <= E2 do {S X=X+1;}}
  macro var E1:Exp, E2:Exp, Es:Exps; = var E1; var E2, Es;
  macro var X : T:Type = E; = var X : T; X = E;


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
form \textit{\#Id:Type}. */

  syntax #Id ::= "object"

  syntax Type ::= "class" #Id [prec 1]

  syntax Decl ::= "method" #Id "(" Exps ")" ":" Type Stmt
                | "method" #Id "(" Exps ")" Stmt
  macro method X:#Id (Es:Exps) S:Stmt = method X(Es) : void S

  syntax Decl ::= "class" #Id "{" Stmts "}"
                | "class" #Id "extends" #Id "{" Stmts "}"
  macro class C:#Id {Ss:Stmts} = class C extends object {Ss}

  syntax Exp ::= Exp "(" Exps ")"      [:strict(2) prec(2):]

  syntax Exp ::= "new" #Id "(" Exps ")" [:strict(2) prec(1):]
               | "this"
               | "super"
               | Exp "." #Id            [:prec(1):]
               | Exp "instanceOf" #Id   [:prec(0) strict(1):]
               | "cast" Exp "to" #Id    [:prec(0) strict(1):]

  syntax Stmt ::= "try" Stmt "catch" "(" Exp ")" Stmt   [:prec(90):]
end module

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
                      <br/>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
                        <return color="LimeGreen"> .K </return>
                          // holds return type
                        <br/>
                        <crntObj color="Fuchsia"> 
                          <crntClass> object </crntClass> 
                          <envStack> .List </envStack>
                          <location multiplicity="?"> .K </location>
                        </crntObj>
                      </control>
                    </thread>
                  </threads>
                  <br/>
                  <store color="white"> .Map </store>
                  <busy color="cyan">.Set</busy>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="brown" stream="stdout"> .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
                  <br/>
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

  syntax Val ::= #Int | #Bool | #String
               | "arrayRef" "(" Type "," #Nat "," #Nat ")"
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

  syntax K ::= "undefined" "(" Type ")" [:latex("\bot_{#1}"):]

  rule <k> var X:#Id : T:Type; => . ...</k>
       <env> Env:Map => Env[L:#Nat/X] </env>
       <store>... . => L |-> undefined(T) ...</store>
       <nextLoc> L => L +Nat 1 </nextLoc>

  rule <k> var X[N:#Nat] : arrayOf T; => . ...</k> 
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> arrayRef(arrayOf T, L +Nat 1, N)
                       L +Nat 1 .. L +Nat N |-> undefined(T) ...</store>
       <nextLoc> L => L +Nat 1 +Nat N </nextLoc>

  context var _[HOLE]:_ ;

  syntax #Id ::= "$1" | "$2"
  rule var X[N1,N2,Vs] : arrayOf arrayOf T; =>
       var X[N1] : arrayOf arrayOf T;
       {
         var $1 : arrayOf arrayOf T = X;
         for $2 = 0 to _-_(N1,1) do       // stupid parser
         {
           (var X[N2,Vs] : arrayOf T;)   // stupid parser
           $1[$2] = X;
         }
       }  [:structural:]

  rule <k> X => V:Val ...</k>
       <env>...X|->L...</env>
       <store>...L|->V...</store> [:transition:]

  context ++(HOLE => lvalue(HOLE))
  rule <k> ++loc(L) => I:#Int +Int 1 ...</k>
       <store>... L |-> (I => I +Int 1) ...</store> [:transition:]

  rule I1:#Int + I2:#Int => I1 +Int I2
  rule Str1:#String + Str2:#String => Str1 +String Str2
  rule _-_(I1,I2) => _-Int_(I1,I2)
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

  rule V[N1,N2,Vs] => V[N1][N2,Vs] [:structural:]
  rule arrayRef(_,L,M:#Nat)[N] => lookup(L +Int N)
    when N >=Nat 0 andBool N <Nat M   [:structural:]

  rule sizeOf(arrayRef(_,_,N)) => N

  syntax Val ::= "nothing"
  rule return; => return nothing;   [:structural:]

  rule <k> read() => I ...</k> <in> ListItem(I) => . ...</in> [:transition:]

  context (HOLE => lvalue(HOLE)) = _

  rule {} => . [:structural:]
  rule <k> {Ss:Stmts} => Ss~>env(Env) ...</k> <env> Env </env> [:structural:]
  rule S1:Stmt S2:Stmt => S1 ~> S2  [:structural:]
  rule V; => .
  rule if  true then S else _ => S
  rule if false then _ else S => S
  rule <k> while E:Exp do S
    => if E then {S while E do S} else {} ...</k> [:structural:]
  rule <k> print(V,Vs=>Vs);...</k> <out>... .=>ListItem(V)</out>
    when typeOf(V) ==Bool int orBool typeOf(V) ==Bool string    [:transition:]
  rule print(.Vals); => . [:structural:]

  rule (<thread>... <k>.K</k> <holds> H:Map </holds> ...</thread> => .)
       <busy> Busy:Set => Busy -Set keys(H) </busy>
  rule <k> acquire V; => . ...</k> <holds>... . => V|->0 ...</holds>
       <busy> Busy (. => SetItem(V)) </busy>
    when notBool(V in Busy)   [:transition:]
  rule <k> acquire V; => . ...</k> <holds>...V|->(N => N +Nat 1)...</holds>
  rule <k> release V; => . ...</k> <holds>...V|->(N => _-Int_(N,1))...</holds>
    when N >Nat 0
  // used prefix notation for -Int because of parsing problems
  rule <k> release V; => . ...</k> <holds>... V|->0 => . ...</holds>
       <busy>... SetItem(V)=>. ...</busy>
  rule <k> rendezvous V; => . ...</k>
       <k> rendezvous V; => . ...</k> [:transition:]

// Auxiliary operations

  syntax Exp ::= "lvalue" "(" K ")"
  syntax Val ::= "loc" "(" #Nat ")"
  rule <k> lvalue(X) => loc(L:#Nat) ...</k>
       <env>... X|->L ...</env>  [:structural:]
  context lvalue(_[HOLE])
  context lvalue(HOLE[_])
  rule <k> lvalue(lookup(L)) => loc(L) ...</k>  [:structural:]
  syntax K ::= "lookup" "(" #Nat ")"
  rule <k> lookup(L) => V ...</k> <store>... L |-> V ...</store> [:transition:]
  syntax K ::= "env" "(" Map ")"
  rule <k> env(Env) => . ...</k> <env> _ => Env </env> [:structural:]
  rule (env(_) => .) ~> env(_) [:structural:]

// typeOf
  syntax Type ::= "typeOf" "(" K ")"
  rule typeOf(I) => int              [:structural:]
  rule typeOf(B) => bool             [:structural:]
  rule typeOf(_:#String) => string   [:structural:]
  rule typeOf(arrayRef(T,_,_)) => T  [:structural:]
  rule typeOf(undefined(T)) => T     [:structural:]
  rule typeOf(nothing) => void       [:structural:]

  syntax Types ::= "types" "(" Exps ")"                [:prec(1):]
  rule types(.Exps) => void,.Types                     [:structural:]
  rule types(X : T) => T,.Types                        [:structural:]
  rule types(X : T, E:Exp, Es:Exps) => T, types(E,Es)  [:structural:]

  syntax List{K} ::= #Nat ".." #Nat
  rule N1:#Nat..N2:#Nat => .List{K}              when N1  >Nat N2 [:structural:]
  rule N1:#Nat..N2:#Nat => N1 ,, (N1 +Nat 1)..N2 when N1 <=Nat N2 [:structural:]

/*@ \subsection{Changes to SIMPLE Semantics}
We extend/change the semantics of several SIMPLE constructs in order
to take advantage of the richer KOOL semantic infrastructure and thus
get more from the existing SIMPLE constructs. */

/*@ \subsubsection{Spawn}
Like in untyped KOOL. */

  rule <thread>... <k> spawn S => . ...</k>
                   <env> Env </env>
                   <crntObj> Obj </crntObj>
       ...</thread>
       (. => <thread>... <k> S </k>
                         <env> Env </env>
                         <crntObj> Obj </crntObj>
             ...</thread>)

/*@ \subsubsection{Assignment}
Typed KOOL allows to assign subtype instance values to supertype lvalues. */

  rule <k> loc(L)=V
        => subtype(typeOf(V),typeOf(K)) ~> true?
           ~> unsafeCast(V,typeOf(K:K))...</k>
       <store>...L|->(K => unsafeCast(V,typeOf(K)))...</store>  [:transition:]

/*@ \subsubsection{Typed exceptions}
Exceptions are propagated now until a catch that can bind them is
encountered. */

  syntax ListItem ::= "(" Exp "," Stmt "," K "," Map "," Bag ")"
  syntax K ::= "popx"
  rule <k> (try S1 catch(X : T) S2 => S1 ~> popx) ~> K </k>
       <control> <xstack> . => (X : T,S2,K,Env,C) ...</xstack> C:Bag </control>
       <env> Env </env>
  rule <k> popx => . ...</k> <xstack> _:ListItem => . ...</xstack>
  rule <k> throw V; ~> _
        => if subtype(typeOf(V), T)
           then {var X : T=V; S2}
           else throw V; ~> K </k>
       <control>
         <xstack> (X : T,S2,K,Env,C) => . ...</xstack>
         (_ => C)
       </control>
       <env> _ => Env </env>

/*@ \subsubsection{bindTo}
\texttt{bindto} also checks the well-formedness of the function
parameters */

  syntax K ::= "bindto" "(" Exps "," Vals ")"
  rule <k> (. => X = V;) ~> bindto((X : T, XTs:Exps => XTs),(V,Vs:Vals => Vs)) 
      ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> undefined(T) ...</store>
       <nextLoc> L => L +Nat 1 </nextLoc>
  rule <k> bindto(.Exps,.Vals) => . ...</k>  [:structural:]


/*@ \subsection{Object and method closures}
The only change to untyped KOOL's values is that closures are now typed
(their last argument holds their type). */

 syntax Val ::= "objectClosure" "(" Bag ")"
              | "methodClosure" "(" #Id "," #Nat "," Exps "," Stmt "," Type ")"

/*@ \subsection{Class declaration}       
Like in untyped KOOL. */

  rule <k> class Class1:#Id extends Class2:#Id { Ss:Stmts } => . <_/k>
       <classes>... (. => <class>
                            <className> Class1 </className>
                            <extends> Class2 </extends>
                            <declarations> Ss </declarations>
                        </class>)
       ...</classes>  [:structural:]

/*@ \subsection{Program initialization}
Like in untyped KOOL. */

  syntax K ::= "execute"
  rule <k> execute => new main(); </k> <env> . </env>  [:structural:]

/*@ \subsection{Method declaration}
Methods are now typed and we need to store their types in their
closures, so that their type contract can be checked at invocation
time.  The rule below is conceptually similar to that of untyped KOOL;
the only difference is the addition of the types.  */

  rule <k> method F:#Id(XTs:Exps) : T S:Stmt => . ...</k>
       <crntClass> Class:#Id </crntClass>
       <location> OL:#Nat </location>
       <env> Env => Env[L/F] </env>
       <store>... 
         .  => L|->methodClosure(Class,OL,XTs,S, function from types(XTs) to T)
       ...</store>
       <nextLoc> L => L +Nat 1 </nextLoc>


/*@ \subsection{New}
The semantics of \texttt{new} in dynamically typed KOOL is also
similar to that in untyped KOOL, the main difference being the
management of the return types.  Indeed, when a new object is created
we also have to stack the current type in the \textsf{return} cell in
order to be recovered after the creation of the new object.  Only the
first rule below needs to be changed; the others are identical to
those in untyped KOOL. */

  rule <k> new Class(Vs) ~> K 
        => create(Class) ~> storeObj ~> _`(_`)(Class,Vs); return this; </k>
       <env> Env => . </env>
       <control> C:Bag
         <crntObj> Obj
                => <crntClass> object </crntClass>
                   <envStack> ListItem(object::<env>.Map</env>) </envStack>
                   <location> L </location>
         </crntObj>
         <return> T => class Class </return>
         <fstack> . => (Env, K, C <return> T </return> 
                                  <crntObj> Obj </crntObj>) ...</fstack>
       </control>
       <nextLoc> L => L +Nat 1 </nextLoc>

  syntax K ::= "create" "(" K ")"
  rule <k> create(Class)
        => create(Class1) ~> setCrntClass(Class) ~> Ss ~> addEnvLayer ...</k>
       <className> Class </className>
       <extends> Class1 </extends>
       <declarations> Ss </declarations>  [:structural:]
  rule <k> create(object) => . ...</k>    [:structural:]

  syntax K ::= "setCrntClass" "(" #Id ")" 
  rule <k> setCrntClass(Class) => . ...</k>
       <crntClass> _ => Class </crntClass>  [:structural:]

  syntax K ::= "addEnvLayer"
  rule <k> addEnvLayer => . ...</k>
       <env> Env => . </env>
       <crntClass> Class </crntClass>
       <envStack> . => ListItem(Class::<env>Env</env>) ...</envStack> 
    [:structural:]

  syntax K ::= storeObj
  rule <k> storeObj => . ...</k>
       <crntObj> Obj (<location> L </location> => .) </crntObj>
       <store>... . => L |-> objectClosure(Obj) ...</store>

/*@ \subsection{Self reference}
Like in untyped KOOL. */

  rule <k> this => objectClosure(Obj) ...</k>
       <crntObj> Obj </crntObj>

/*@ \subsection{Object member access}
Like in untyped KOOL. */

  rule <k> X => _._(this,X) ...</k> <env> Env </env>
    when notBool(X in keys(Env))  [:structural:]
  context ('_._(HOLE:K,,_)) when (HOLE:K =/=Bool super)
  rule <k> _._(objectClosure(<crntClass> Class </crntClass>
                   <envStack>...ListItem(Class :: EnvC) EStack </envStack>),X) 
        => lookupMember(<envStack>ListItem(Class :: EnvC) EStack</envStack>, X)
       ...</k>  [:structural:]
  rule <k> _._(super,X) => lookupMember(<envStack>EStack</envStack>,X)...</k>
       <crntClass> Class:#Id </crntClass>
       <envStack>... ListItem(Class :: EnvC) EStack </envStack>
    [:structural:]


/*@\subsection{Method invocation}
The method lookup is the same as in untyped KOOL.
The method closure application and return are slightly different,
since we need to check that the type of the returned value is an
instance of the claimed return type of the method.  The first group of
rules below are identical to those in untyped KOOL. */

  rule <k> _`(_`)((X => V),_) ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V ...</env>

  rule <k> _`(_`)((X => _._(this,X)),_) ...</k>
       <env> Env </env>
    when notBool(X in keys(Env))  [:structural:]

  context '_`(_`)('_._(HOLE:K,,_),,_) when HOLE:K =/=Bool super 

  rule <k> '_`(_`)(('_._(objectClosure(Obj <envStack> EStack </envStack>),,X) 
        => lookupMember(<envStack> EStack </envStack>, X)),,_) ...</k>
    [:structural:]

  rule <k> '_`(_`)(('_._(super,,X) 
        => lookupMember(<envStack> EStack </envStack>, X)),,_) ...</k>
       <crntClass> Class:#Id </crntClass>
       <envStack>... ListItem(Class :: _) EStack </envStack>
    [:structural:]

  context '_`(_`)(HOLE:K,,_)
       when getKLabel HOLE:K ==Bool '_`(_`) orBool
          getKLabel HOLE:K ==Bool '_`[_`]

  rule <k> '_`(_`)((lookup(L) => V),,_) ...</k>
       <store>... L |-> V ...</store>

  syntax ListItem ::=  "(" Map "," K "," Bag ")"

/*@ Closure application needs to also set a new return type in the
\textsf{return} cell, in order for the values returned by its body to
be checked against the return type of the method.  To do this correctly,
we also need to stack the current status of the \textsf{return} cell
and then pop it when the method returns. */

  rule <k> _`(_`)(methodClosure(Class,OL:#Nat,XTs,S:Stmt,function from _ to T),
                  Vs:Vals) ~> K:K
        => bindto(XTs,Vs) ~> S ~> return; </k>
       <control> C:Bag 
          <fstack> . => (Env,K,C <crntObj> Obj' </crntObj>
                                 <return> T' </return>) ...</fstack> 
          <crntObj> Obj':Bag => <crntClass>Class</crntClass> Obj </crntObj>
          <return> T':Type => T </return>
        </control>
       <env> Env => . </env>
       <store>... OL |-> objectClosure(<crntClass>_:#Id</crntClass>Obj:Bag)
       ...</store>

/*@ At method return, we have to check that the type of the returned
value is a subtype of the expected return type.  Moreover, if that is
the case, then we also upcast the returned value to one of the
expected type. */

   rule <k> return V; ~> _ 
         => subtype(typeOf(V),T) ~> true? ~> unsafeCast(V,T)~> K </k>
       <control>
         <fstack> (Env,K,C) => . ...</fstack>
         (<return> T </return> _ => C)
       </control>
       <env> _ => Env </env>


/*@ \subsection{Instance Of}
Like in untyped KOOL. */

  rule objectClosure((_ <envStack>ListItem(Class::_)...</envStack>))
        instanceOf Class => true
  rule objectClosure((_ <envStack> ListItem(Class1::_)
                       => . ...</envStack>)) instanceOf Class2 
    when Class1 =/=Bool Class2  [:structural:]
  rule objectClosure((_ <envStack> .List </envStack>)) instanceOf Class
    => false
 
/*@ \subsection{Cast}
Unlike in untyped KOOL, in typed KOOL we actually check that the object
can indeed be cast to the claimed type. */

  rule <k> cast objectClosure((<crntClass> _:K </crntClass> Obj)) to Class 
        => objectClosure(Obj) instanceOf Class ~> true?
             ~> objectClosure(<crntClass> Class </crntClass> Obj) ...</k>
    [:structural:]

/*@ \subsection{Objects as lvalues}
Like in untyped KOOL. */

  rule <k> lvalue(X => _._(this,X)) <_/k> <env> Env </env>
    when notBool(X in keys(Env))  [:structural:]

  context lvalue(_._(HOLE,_))
  rule <k> lvalue(_._(objectClosure(<crntClass> Class </crntClass> 
                           <envStack>...
                             ListItem(Class :: EnvC) EStack
                           </envStack>), X)
        => lookupMember(<envStack>ListItem(Class :: EnvC:BagItem) EStack:List
                        </envStack>, X)) 
       ...</k>  [:structural:]

/*@ \subsection{Lookup member}
Like in untyped KOOL. */

  syntax K ::= #Id "::" BagItem
  syntax K ::= "lookupMember" "(" BagItem "," #Id ")"
  rule lookupMember(<envStack> ListItem(_ :: <env>...X|->L...</env>)
                    ...</envStack>,X) => lookup(L)  [:structural:]
  rule lookupMember(<envStack> ListItem(_ :: <env> Env </env>)
                            => . ...</envStack>, X)
    when notBool(X in keys(Env))                      [:structural:]

//@ \subsection{Auxilliary operations and rules}

/*@ \subsubsection{\texttt{typeOf}}
\texttt{typeOf} for the additional values. */

  rule typeOf(objectClosure(_ <envStack> ListItem(Class::_) ...</envStack>))
    => class Class [:structural:]
  rule typeOf(methodClosure(_,_,_,_,T)) => T  [:structural:]

/*@ \subsubsection{Subtyping constraints}
The subclass relation introduces a subtyping relation. */

  syntax Exp ::= "subtype" "(" Types "," Types ")"

  rule subtype(T,T) => true  [:structural:]
  rule <k> subtype(class Class1, class Class)
        => subtype(class Class2, class Class) ...</k>
       <className> Class1 </className> <extends> Class2 </extends>
    when Class1 =/=Bool Class  [:structural:]
  rule subtype((T1:Type,T2:Type,Ts:Types),(T1':Type,T2':Type,Ts':Types))
    => subtype(T1,T1') ~> true? ~> subtype((T2,Ts),(T2',Ts'))  [:structural:]
  rule subtype(.Types,.Types) => true  [:structural:]

/*@ \subsubsection{Unsafe Casting}
Performs unsafe casting.  One should only use it in combination with
the subtype relation above.  */

  syntax Val ::= unsafeCast( Val , Type )
  rule unsafeCast(objectClosure(<crntClass>_:K </crntClass> Obj), class Class)
    => objectClosure(<crntClass> Class </crntClass> Obj)
    [:structural:]
  rule unsafeCast(V,T) => V when typeOf(V) ==Bool T  [:structural:]

/*@ \subsubsection{Generic guard}
A generic computational guard (should be builtin): it allows the
computation to continue only if a prefix guard evaluates to true.  */

  syntax K ::= "true?"
  rule true ~> true? => .  [:structural:]

end module
