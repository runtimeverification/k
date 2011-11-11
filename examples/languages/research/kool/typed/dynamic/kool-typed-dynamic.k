module KOOL-TYPED-DYNAMIC-SYNTAX
  syntax #Id ::= "main"
//@ KOOL addition: the ``object'' class  
  syntax #Id ::= "object"


  syntax Type ::= "int"
                | "bool"
                | "string"
                | "void"
                | "array" "of" Type [:prec(1):]
                | "function" "from" Types "to" Type
                    [:prec(1) latex "{#1}\rightarrow{#2}":]
//@ KOOL addition: types for objects
  syntax Type ::= "class" #Id [prec 1]
   
  syntax Types ::= List{Type,","}

  syntax Decl ::= "var" Exps ";"
//@ KOOL additions: function is renamed into method and classes are introduced.
  syntax Decl ::= "method" #Id "(" Exps ")" ":" Type Stmt
                | "method" #Id "(" Exps ")" Stmt
                | "class" #Id "{" Stmts "}" [prec 0]
                | "class" #Id "extends" #Id "{" Stmts "}"

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
               | Exp "(" Exps ")"      [:strict(2) prec(2):]
               | "read" "(" ")"
               | Exp "=" Exp           [:strict(2) prec(40) gather (e E):]
               | Exp ":" Type          [:prec(10):]
                                       // allowed only for declarations

//@ Kool additions: new, this, super, object space, instanceOf, cast
  syntax Exp ::= "new" #Id "(" Exps ")" [:strict(2) prec(1):]
               | "this"
               | "super"
               | Exp "." #Id            [:prec(2):]
               | Exp "instanceOf" #Id   [:prec(0) strict(1):]
               | "cast" Exp "to" #Id    [:prec(0) strict(1):]

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
                | "try" Stmt "catch" "(" Exp ")" Stmt   [:prec(90):]
                | "throw" Exp ";"                       [:strict:]
                | "spawn" Stmt                          [:prec(90):]
                | "acquire" Exp ";"                     [:strict:]
                | "release" Exp ";"                     [:strict:]
                | "rendezvous" Exp ";"                  [:strict:]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts            [:seqstrict prec(100) gather(e E):]

  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X:#Id = E1 to E2 do S) = {var X:int=E1; while X <= E2 do {S X=X+1;}}
  macro var E1:Exp, E2:Exp, Es:Exps; = var E1; var E2, Es;
  macro var X : T:Type = E; = var X : T; X = E;
  macro class C:#Id {Ss:Stmts} = class C extends object {Ss}
  macro method X:#Id (Es:Exps) S:Stmt = method X(Es) : void S
end module

module KOOL-TYPED-DYNAMIC
  imports KOOL-TYPED-DYNAMIC-SYNTAX
  syntax Val ::= #Int | #Bool | #String
               | "array" "(" Type "," #Nat "," #Nat ")"

/*@ KOOL additions:  lambda now takes current object as first argument.

Also introducing the object value ``obj''.*/
  syntax Val ::= "lambda" "(" K "," Exps "," Stmt "," Type ")"
               | "obj" "(" Bag ")"
               | "objRef" "(" #Id "," #Nat ")" 

  syntax Exp ::= Val
  syntax KResult ::= Val

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
// KOOL addition
                        <crntObj color="Fuchsia"> 
                          <crntClass> object </crntClass> 
                          <envStack> .List </envStack>
                          <location multiplicity="?"> .K </location>
                        </crntObj>
                      </control>
                    </thread>
                  </threads>
                  <br/>
                  <genv color="pink"> .Map </genv>
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

  syntax K ::= "undefined" "(" Type ")" [:latex("\bot_{#1}"):]

  rule <k> var X:#Id : T:Type; => . ...</k>
       <env> Env:Map => Env[L:#Nat/X] </env>
       <store>... . => L |-> undefined(T) ...</store>
       <nextLoc> L => L +Nat 1 </nextLoc>

  rule <k> var X[N:#Nat] : array of T; => . ...</k> 
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> array(array of T, L +Nat 1, N)
                       L +Nat 1 .. L +Nat N |-> undefined(T) ...</store>
       <nextLoc> L => L +Nat 1 +Nat N </nextLoc>

  context var _[[HOLE]]:_ ;

  syntax Vals ::= List{Val,","}

  context var _[[HOLE]]:_ ;

  syntax #Id ::= "$1" | "$2"
  rule var X[N1,N2,Vs] : array of array of T; =>
       var X[N1] : array of array of T;
       {
         var $1 : array of array of T = X;
         for $2 = 0 to _-_(N1,1) do       // stupid parser
         {
           (var X[N2,Vs] : array of T;)   // stupid parser
           $1[$2] = X;
         }
       }  [:structural:]

  rule <k> method F:#Id(XTs:Exps) : T S:Stmt => . ...</k>
       <crntClass> Class:#Id </crntClass>
       <location> OL:#Nat </location>
       <env> Env => Env[L/F] </env>
       <store>... 
         .  => L|->lambda(objRef(Class,OL),XTs,S, function from types(XTs) to T)
       ...</store>
       <nextLoc> L => L +Nat 1 </nextLoc>

//@ \subsection{Class declaration}       
  rule <k> class Class1:#Id extends Class2:#Id { Ss:Stmts } => . <_/k>
       <classes>... (. => <class>
                            <className> Class1 </className>
                            <extends> Class2 </extends>
                            <declarations> Ss </declarations>
                        </class>)
       ...</classes>

  syntax K ::= "execute"
  rule <k> execute => new main(); </k> <env> . </env>

  rule <k> X => V:Val ...</k>
       <env>...X|->L...</env>
       <store>...L|->V...</store> [:transition:]

// KOOL addition       
// to avoid parsing ambiguity, use _._(this,X) instead of this.X
  rule <k> X => _._(this,X) ...</k>
       <env> Env </env>
    if notBool(X in keys(Env))

  context ++([HOLE] => l-value([HOLE]))
  rule <k> ++loc(L) => I:#Int +Int 1 ...</k>
       <store>... L |-> (I => I +Int 1) ...</store> [:transition:]

  rule I1:#Int + I2:#Int => I1 +Int I2
  rule Str1:#String + Str2:#String => Str1 +String Str2
  rule _-_(I1,I2) => _-Int_(I1,I2)
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 if I2 =/=Bool 0
  rule I1 % I2 => I1 %Int I2 if I2 =/=Bool 0
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

//@ Check array bounds, as part of the dynamic typing policy.

  rule V[N1,N2,Vs] => V[N1][N2,Vs] [:structural:]
  rule array(_,L,M:#Nat)[N] => lookup(L +Int N)
    if N >=Nat 0 andBool N <Nat M   [:structural:]
  rule sizeOf(array(_,_,N)) => N

/*@\subsection{Method call}
SKOOL has dynamic method dispatch, like most OO languages.
There are several cases to treat, though.

Case 1: method is called directly, not through an object or super.
Then "this" is assumed */

  rule <k> _`(_`)((X => _._(this,X)),_) ...</k>

--- We would like to write the rule above as
---   rule <k> (X => _._(this,X))(_) <_/k>
--- or even
---   rule <k> (X => this.X)(_) <_/k>
--- but, unfortunately, our current Maude-based parser does not allow it
--- Same applies to the other rules below

/*@ Case 2: method is called through an object or super.
There are two subcases:

Case 2.1: called through a proper object (not super), so dynamic dispatch.
Then evaluate the object espression and lookup method from top of its
environment. */

  context '_`(_`)('_._(`[HOLE`]:K,,_),,_) if `[HOLE`]:K =/=Bool super 

  rule <k> '_`(_`)(('_._(obj(Obj <envStack> EStack:List </envStack>),,X) 
        => lookupMember(<envStack> EStack </envStack>, X)),,_) ...</k>

//@ Case 2.2: called through super, so static dispatch from parent class
  rule <k> '_`(_`)(('_._(super,,X) 
        => lookupMember(<envStack> EStack </envStack>, X)),,_) ...</k>
       <crntClass> Class:#Id </crntClass>
       <envStack>... ListItem(Class :: _) EStack </envStack>

/*@ Eventually, each of the rules above produces a lookup(L) instead of 
the method. When that happens, just lookup the function value at location L. */

  rule <k> '_`(_`)((lookup(L) => V),,_) ...</k>
       <store>... L |-> V ...</store>

  syntax ListItem ::=  "(" Map "," K "," Bag ")"


  rule <k> _`(_`)(lambda(objRef(Class,OL:#Nat),XTs,S:Stmt, function from _ to T), Vs:Vals) ~> K:K 
        => bindto(XTs,Vs) ~> S ~> return; </k>
       <control> C:Bag 
          <fstack> . => (Env,K,C <return> T' </return> <crntObj> Obj' </crntObj>) ...</fstack> 
          <crntObj> Obj':Bag => <crntClass>Class</crntClass> Obj </crntObj>
          <return> T':Type => T </return>
        </control>
       <env> Env => . </env>
       <store>... OL |-> obj(<crntClass>_:#Id</crntClass>Obj:Bag) ...</store>

   rule <k> return V; ~> _ => upcast(V,T) when subtype(typeOf(V),T) ~> K </k>
       <control>
         <fstack> (Env,K,C) => . ...</fstack>
         (<return> T </return> _ => C)
       </control>
       <env> _ => Env </env>

  syntax Val ::= "nothing"
  rule return; => return nothing;   [:structural:]

  rule <k> read() => I ...</k> <in> ListItem(I) => . ...</in> [:transition:]

  context ([HOLE] => l-value([HOLE])) = _
  rule <k> loc(L)=V 
          => upcast(V,typeOf(K:K)) when subtype(typeOf(V),typeOf(K)) ...</k> 
       <store>... L|->(K=>upcast(V,typeOf(K))) ...</store> [:transition:]

/*@ \subsection{New}
 The semantics of new consists of two actions: memory allocation for
the new object and the execution of the corresponding constructor.

The current environment and object are stored on the stack and
recovered after new, because new destroys them. */

  rule <k> new Class(Vs) ~> K 
        => create(Class) ~> storeObj ~> _`(_`)(Class,Vs); return this; </k>
       <env> Env => . </env>
       <control> C:Bag
         <crntObj> Obj => <crntClass> object </crntClass>
                          <envStack> ListItem(object::<env>.Map</env>) </envStack>
                          <location> L </location>
         </crntObj>
         <return> T => class Class </return>
         <fstack> . => (Env, K, C <return> T </return> 
                                  <crntObj> Obj </crntObj>) ...</fstack>
       </control>
       <nextLoc> L => L +Nat 1 </nextLoc>

/*@ Create a new object (memory allocation)

A memory object representation is a layered structure: for each class on the
path from the instance class to the root of the hierarchy there is a layer 
including the memory allocated for the members (both fields and methods) of 
that class.
Even though "create" is an auxilliary operation, it is used only here. */

  syntax K ::= "create" "(" K ")"

  rule <k> create(Class)
        => create(Class1) ~> setCrntClass(Class) ~> Ss ~> addEnvLayer ...</k>
       <className> Class </className>
       <extends> Class1 </extends>
       <declarations> Ss </declarations>
  rule <k> create(object) => . ...</k>

//@ Add a new tagged environment layer to the current object.
--- This is an auxilliary operation, but is used only here.
  syntax K ::= "addEnvLayer"
  rule <k> addEnvLayer => . ...</k>
       <env> Env => . </env>
       <crntClass> Class </crntClass>
       <envStack> . => ListItem(Class::<env>Env</env>) ...</envStack> 

/*@ Set the current class of the current object.
This is necessary to be done at each layer, because the current object is 
enclosed as part of the function values (see the semantics of method 
declarations above). */

  syntax K ::= "setCrntClass" "(" #Id ")" 
  rule <k> setCrntClass(Class) => . ...</k>
       <crntClass> _ => Class </crntClass>

  syntax K ::= storeObj
  rule <k> storeObj => . ...</k>
       <crntObj> Obj (<location> L </location> => .) </crntObj>
       <store>... . => L |-> obj(Obj) ...</store>

//@ Self reference via "this"
  rule <k> this => obj(Obj) ...</k>  
       <crntObj> Obj </crntObj>

 
//@ Self reference via "this"
  rule <k> this => obj(Obj) ...</k>  
       <crntObj> Obj </crntObj>


/*@ \subsection{Object member access}
There are two cases, like for method dispatch:

Case 1: member access through a proper object (not super);
Then evaluate the object expression and lookup member starting with current
class (static scoping). */

  context ('_._(`[HOLE`]:K,,_)) if (`[HOLE`]:K =/=Bool super)
  rule <k> _._(obj(<crntClass> Class </crntClass> <envStack>...ListItem(Class :: EnvC:BagItem) EStack </envStack>),X) 
        => lookupMember(<envStack> ListItem(Class :: EnvC) EStack </envStack>, X)
       ...</k>

//@ Case 2: member access through super
  rule <k> _._((super => obj(Obj  <crntClass> Class2 </crntClass>)),X) ...</k>
       <crntObj> Obj <crntClass> Class1 </crntClass> </crntObj>
       <className> Class1 </className>
       <extends> Class2 </extends>

  rule obj((_ <envStack> ListItem(Class::_) ...</envStack>)) instanceOf Class 
    => true
  rule obj((_ <envStack> ListItem(Class1::_) => . ...</envStack>)) instanceOf Class2 
    if Class1 =/=Bool Class2
  rule obj((_ <envStack> .List </envStack>)) instanceOf Class
    => false
 
  rule <k> cast obj((<crntClass> _:K </crntClass> Obj)) to Class 
        => obj(<crntClass> Class </crntClass> Obj) when obj(Obj) instanceOf Class ...</k>

 rule {} => . [:structural:]
  rule <k> {Ss:Stmts} => Ss~>env(Env) ...</k> <env> Env </env> [:structural:]
  rule S1:Stmt S2:Stmt => S1 ~> S2
  rule V; => .
  rule if  true then S else _ => S
  rule if false then _ else S => S
  rule <k> while E:Exp do S
    => if E then {S while E do S} else {} ...</k> [:structural:]
//@ We only allow printing integers and strings
  rule <k> print(V,Vs=>Vs);...</k> <out>... .=>ListItem(V)</out>
    if typeOf(V) ==Bool int orBool typeOf(V) ==Bool string    [:transition:]
  rule print(); => . [:structural:]

  syntax ListItem ::= "(" Exp "," Stmt "," K "," Map "," Bag ")"
  syntax K ::= "popx"
  rule <k> (try S1 catch(X : T) S2 => S1 ~> popx) ~> K </k>
       <control> <xstack> . => (X : T,S2,K,Env,C) ...</xstack> C:Bag </control>
       <env> Env </env>
  rule <k> popx => . ...</k> <xstack> _:ListItem => . ...</xstack>
  rule <k> throw V; ~> _ => if subtype(typeOf(V), T) then {var X : T=V; S2} else throw V; ~> K </k>
       <control> <xstack> (X : T,S2,K,Env,C) => . ...</xstack> (_ => C) </control>
       <env> _ => Env </env>

   rule <thread>... <k> spawn S => . ...</k> <env> Env </env> ...</thread>
        (. => <thread>... <k> S </k> <env> Env </env> ...</thread>)
   rule (<thread>... <k>.K</k> <holds> H:Map </holds> ...</thread> => .)
        <busy> Busy:Set => Busy -Set keys(H) </busy>
   rule <k> acquire V; => . ...</k> <holds>... . => V|->0 ...</holds>
        <busy> Busy (. => SetItem(V)) </busy>
     if notBool(V in Busy)   [:transition:]
   rule <k> acquire V; => . ...</k> <holds>... V|->(N => N +Nat 1) ...</holds>
   rule <k> release V; => . ...</k> <holds>... V|->(N => _-Int_(N,1)) ...</holds>
     if N >Nat 0
   // used prefix notation for -Int because of parsing problems
   rule <k> release V; => . ...</k> <holds>... V|->0 => . ...</holds>
        <busy>... SetItem(V)=>. ...</busy>
   rule <k> rendezvous V; => . ...</k> <k> rendezvous V; => . ...</k> [:transition:]

//@ \subsection{Auxiliary operations}

//@ \texttt{l-value}
  syntax Exp ::= "l-value" "(" K ")"
  syntax Val ::= "loc" "(" #Nat ")"
  rule <k> l-value(X) => loc(L:#Nat) ...</k> <env>... X|->L ...</env>
//@ KOOL addiiton: Implicit member access
  rule <k> l-value(X => _._(this,X)) <_/k> <env> Env </env> if notBool(X in keys(Env))

  context l-value(_[[HOLE]])
  context l-value([HOLE][_])

/*@\paragraph{Explicit member access}
First evaluate the object, then lookup its corresponding member staticaly.
lookupMember is defined below; it evaluates to a lookup(L), also defined below,
where L points to the actual member value.
Note that object values are envStack cells, and that lookupMember takes such
cells as first argument; these cells are also defined below.*/
  context l-value(_._([HOLE],_))
  rule <k> l-value(_._(obj(<crntClass>Class </crntClass> 
                           <envStack>...ListItem(Class :: EnvC) EStack </envStack>), X)
        => lookupMember(<envStack>ListItem(Class :: EnvC:BagItem) EStack:List
                        </envStack>, X)) 
       ...</k>


    rule <k> l-value(lookup(L)) => loc(L) ...</k>

//@ \texttt{lookup}
  syntax K ::= "lookup" "(" #Nat ")"
  rule <k> lookup(L) => V ...</k> <store>... L |-> V ...</store> [:transition:]

//@ \texttt{bindto} also checks the well-formedness of the function parameters
  syntax K ::= "bindto" "(" Exps "," Vals ")"
  rule <k> (. => X = V;) ~> bindto((X : T, XTs:Exps => XTs),(V,Vs:Vals => Vs)) 
      ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> undefined(T) ...</store>
       <nextLoc> L => L +Nat 1 </nextLoc>
  rule <k> bindto(.Exps,.Vals) => . ...</k>

//@ \texttt{env}
  syntax K ::= "env" "(" Map ")"
  rule <k> env(Env) => . ...</k> <env> _ => Env </env> [:structural:]
  rule (env(_) => .) ~> env(_) [:structural:]

//@ \texttt{typeOf}
  syntax Type ::= "typeOf" "(" K ")"
  rule typeOf(I) => int       [:structural:]
  rule typeOf(B) => bool      [:structural:]
  rule typeOf(_:#String) => string  [:structural:]

  rule typeOf(array(T,_,_)) => T  [:structural:]
  rule typeOf(lambda(_,_,_,T)) => T  [:structural:]

  rule typeOf(undefined(T)) => T [:structural:]
  rule typeOf(nothing) => void  [:structural:]

  rule typeOf(obj(_ <envStack> ListItem(Class::_) ...</envStack>)) => class Class
     [:structural:]


  syntax Types ::= "types" "(" Exps ")"    [:prec(1):]
  rule types() => .Types                   [:structural:]
  rule types(X : T, XTs) => T, types(XTs)  [:structural:]

//@ Sequences of locations

  syntax List{K} ::= #Nat ".." #Nat
  rule N1:#Nat..N2:#Nat => .List{K}              if N1  >Nat N2 [:structural:]
  rule N1:#Nat..N2:#Nat => N1 ,, (N1 +Nat 1)..N2 if N1 <=Nat N2 [:structural:]


/*@\subsection{Conditional Pass}  
Allows the process to continue only if the expression evaluates to true.
Useful for checking side conditions to typing rules.
*/

  syntax K ::= K "when" K  [:strict(2):]
  rule K:K when true => K

/*@\subsection{Subtyping constraints}
The subclass relation introduces a subtyping relation.  
*/
  syntax Exp ::= "subtype" "(" Types "," Types ")"

  rule subtype(,) => true
  rule subtype((T1:Type,T2:Type,Ts:Types),(T1':Type,T2':Type,Ts':Types))
    => subtype((T2,Ts),(T2',Ts')) when subtype(T1,T1')
  rule subtype(T,T) => true
  rule <k> subtype(class Class1:#Id, class Class)
        => subtype(class Class2, class Class) ...</k>
      <class>...
          <className> Class1 </className> <extends> Class2 </extends>
      ...</class>
    if Class1 =/=Bool Class
  rule <k> subtype(class Class1, class Class)
        => subtype(class Class2, class Class) ...</k>
          <className> Class1 </className> <extends> Class2 </extends>
    if Class1 =/=Bool Class


//@\subsection{UpCasting}
  syntax Val ::= upcast( Val , Type )
  rule upcast(obj(<crntClass> _:K </crntClass> Obj),class Class) 
       => obj(<crntClass> Class </crntClass> Obj)
    [:structural:]

  rule upcast(V,T) => V if typeOf(V) ==Bool T                  [:structural:]

  syntax K ::= #Id "::" BagItem   
  // Id is the class name, BagItem is its corresp. environment
  syntax K ::= "lookupMember" "(" BagItem "," #Id ")"  
  // BagItem is the envStack cell, Id is the member name

// First look for the member in the top environment; if found then done.
  rule lookupMember(<envStack> ListItem(_ :: <env>... X|->L ...</env>) ...</envStack>,X) 
    => lookup(L)
/// Otherwise, recurse through the object environment stack
  rule lookupMember(<envStack> ListItem(_ :: <env> Env </env>)  => . ...</envStack>, X)
    if notBool(X in keys(Env)) [structural]

end module
