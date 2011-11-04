module KOOL-TYPED-STATIC-SYNTAX
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
  syntax Type ::= "class" #Id 
   
  syntax Types ::= List{Type,","}

  syntax Decl ::= "var" Exps ";"
//@ KOOL additions: function is renamed into method and classPass are introduced.
  syntax Decl ::= "method" #Id "(" Exps ")" ":" Type Stmt
                | "class" #Id "{" Stmts "}"
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
               | Exp "(" Exps ")"      [:strict prec(2):]
               | "read" "(" ")"
               | Exp "=" Exp           [:strict(2) prec(40) gather (e E):]
               | Exp ":" Type          [:prec(10):]
                                       // allowed only for declarations

// Kool additions: new, this, super, object space, instanceOf, cast
  syntax Exp ::= "new" #Id "(" Exps ")" [:strict(2) prec(1):]
               | "this"
               | "super"
               | Exp "." #Id            [:prec(0):]
               | Exp "instanceOf" #Id   [:prec(0) strict(1):]
               | "cast" Exp "to" #Id    [:prec(0) strict(1):]

   syntax Exps ::= List{Exp,","}

  syntax Stmt ::= "{" "}"
                | "{" Stmts "}"
                | Exp ";"                               [:strict prec(45):]
                | "if" Exp "then" Stmt "else" Stmt      [:strict prec(90):]
                | "if" Exp "then" Stmt                  [:prec(89):]
                | "while" Exp "do" Stmt                 [:strict prec(90):]
                | "for" #Id "=" Exp "to" Exp "do" Stmt  [:prec(90):]
                | "return" Exp ";"                      [:strict:]
                | "return" ";"
                | "print" "(" Exps ")" ";"              [:strict:]
                | "try" Stmt "catch" "(" #Id ")" Stmt   [:strict(1) prec(90):]
                | "throw" Exp ";"                       [:strict:]
                | "spawn" Stmt                          [:strict prec(90):]
                | "acquire" Exp ";"                     [:strict:]
                | "release" Exp ";"                     [:strict:]
                | "rendezvous" Exp ";"                  [:strict:]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts            [:seqstrict prec(100) gather(e E):]

  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X:#Id = E1 to E2 do S) = {var X:int=E1; while X <= E2 do {S X=X+1;}}
  macro var E1:Exp, E2:Exp, Es:Exps; = var E1; var E2, Es;
  macro class C:#Id {Ss:Stmts} = class C extends object {Ss}
end module 


module KOOL-TYPED-STATIC
  imports KOOL-TYPED-STATIC-SYNTAX

  syntax Exp ::= Type
  syntax Stmt ::= Type
  syntax KResult ::= Type
  
  configuration <T color="red">
                  <task multiplicity="*" color="yellow">
                    <k color="green"> $PGM:Stmts </k>
                    <tenv color="cyan" multiplicity="?"> .Map </tenv>
                    <return multiplicity="?"> .K </return>
                    <pass> globalPass </pass>
                    <crntClass multiplicity="?"> .K </crntClass>
                  </task>
                  <class multiplicity="+"> 
                    <className> object </className>
                    <extends multiplicity="?"> object </extends>
                    <ctenv multiplicity="?"> .Map </ctenv>
                  </class>
                </T>

  syntax Pass ::= globalPass | classPass | methodPass 
  syntax K ::= Pass

  syntax Type ::= "stmt"

  rule <k> class C:#Id extends C':#Id { Ss:Stmts } => . ...</k> 
       <pass> globalPass </pass>
       (. => <class>... <className> C </className> <extends> C' </extends> 
             ...</class>)
       (. => <task>... 
                <k>  Ss:Stmts </k>
                <pass> classPass </pass>
                <crntClass> C </crntClass>
                <tenv> .Map </tenv>
             ...</task>)

  rule <task>... <k> .K </k> <pass> globalPass </pass> ...</task>  => .

  rule var X:#Id : T:Type ; => bindto(X,T)
  context var _[[HOLE]] : _;
  rule var X[Ts:Types] : T; => checkDepth(Ts,T) ~> bindto(X,T)

  rule <k> method M:#Id(XTs:Exps) : T S:Stmt =>
           bindto(M, function from types(XTs) to T) ...</k>
       <crntClass> C </crntClass>
       (. => <task>
               <k> (var XTs;) S </k>
               <tenv> . </tenv>
               <return> T </return>
               <crntClass> C </crntClass>
               <pass> methodPass </pass>
             </task>)

  rule (<task>... <k> .K </k> <tenv> Rho:Map </tenv> 
                 <crntClass> C </crntClass> <pass> classPass </pass>
       ...</task> => .)
       <class>... <className> C </className> 
                  (. => <ctenv> Rho </ctenv>)
       ...</class>

  rule <k> I:#Int => int ...</k>
  rule <k> B:#Bool => bool ...</k>
  rule <k> Str:#String => string ...</k>
  rule <k> X => T ...</k> <tenv>... X |-> T ...</tenv> <pass> methodPass </pass>
  rule <k> X => _._(this,X) ...</k> <tenv> Rho </tenv> <pass> methodPass </pass>
    if notBool(X in keys(Rho))

  context ++([HOLE] => l-type([HOLE]))
  rule ++ int => int
  rule int + int => int
  rule string + string => string
  rule _-_(int,int) => int
  rule int * int => int
  rule int / int => int
  rule int % int => int
  rule - int => int
  rule int < int => bool
  rule int <= int => bool
  rule int > int => bool
  rule int >= int => bool
  rule T == T => bool
  rule T != T => bool
  rule bool and bool => bool
  rule bool or bool => bool
  rule not(bool) => bool
  rule (array of T)[int,Ts] => T[Ts]
  rule T[] => T
  rule sizeOf(array of T) => int
  rule <k> _`(_`)(function from Ts to T, Ts':Types) 
        => T when subtype(Ts',Ts) ...</k> <pass> methodPass </pass>
  rule read() => int

  context ([HOLE] => l-type([HOLE])) = _
  rule T=T':Type => T when subtype(T', T)


/*@ \subsection{``new'' Operator}
To type ``new'' we only need to check that the class constructor can be
called with arguments of the given type. */
  rule new C(Ts) => _`(_`)(_._((class C), C), Ts)

//@ ``this'' types to the current class
  rule <k> this => class C ...</k>
       <crntClass> C </crntClass>

/*@ ``super'' types to the parent class.
 Note that for typing concerns super can be considered as an object */
   rule <k> super => class C' ...</k> <crntClass> C </crntClass>
       <className> C </className> <extends> C' </extends>
      
/*@\subsection{Object member access}

Case 1: member declared in current class: */
  rule <k> _._(class C,X) => T <_/k>
      <className> C </className> <ctenv_> X |-> T <_/ctenv>
 
/*@ Case 2: member not declared in current class; check parent class.
This currently assumes there are no cycles in the class hierarchy. */
  rule <k> _._(class (C1 => C2),X) <_/k>
      <className> C1:#Id </className> <extends> C2:#Id </extends> 
      <ctenv> Rho </ctenv>
      if notBool(X in keys(Rho)) [structural]

/*\subsection{``instanceOf'' and ``cast''}
As it is hard to check statically whether casting is always safe,
we here trust the user. */

  rule  (class C1) instanceOf C2 => bool

--- Casting
  rule cast (class C1) to C2 => (class C2) 

  rule {} => stmt
  rule <k> {Ss:Stmts} => Ss ~> tenv(Rho) ...</k> <tenv> Rho </tenv>
  rule T; => stmt
  rule if bool then stmt else stmt => stmt
  rule while bool do stmt  => stmt
  rule <k> return T; => stmt when subtype(T,T') ...</k> <return> T' </return>
  rule return; => stmt
  rule print(int,Ts => Ts);
  rule print(string,Ts => Ts);
  rule print(); => stmt
  rule try stmt catch(X) S => {var X:int; S}   [:structural:]
  rule throw int; => stmt
  rule spawn stmt => stmt
  rule acquire T; => stmt
  rule release T; => stmt
  rule rendezvous_;(T) => stmt

  rule stmt stmt => stmt


  syntax Exp ::= Type "when" Exp  [:strict(2):]
  rule T when true => T

  syntax Exp ::= "subtype" "(" Types "," Types ")"

  rule subtype(,) => true
  rule subtype((T,Ts),(T',Ts':Types)) => subtype(T,T') and subtype(Ts,Ts')
  rule subtype(T,T) => true
  rule <k> subtype(class C1, class C)
        => subtype(class C2, class C) ...</k>
       <className> C1 </className> <extends> C2 </extends>
  

/*
  syntax Exp ::= "ordered" "(" Type "," Type ")"
  rule ordered(T,T) => true
  rule ordered(class C1, class C2) 
    => orderedClass(class C1, class C2, class C1, class C2)

  syntax Exp ::= "orderedClass" "(" Type "," Type "," Types "," Types ")"
  
  rule orderedClass(T,_,_,(T,Ts')) => true
  rule orderedClass(_,T',(T',Ts),_) => true
  rule <k> orderedClass(T,_,_,((class C1),Ts' => (class C2),(class C1),Ts')) ...</k>
       <className> C1 </className> <extends> C2 </extends>
    if  T =/=Bool (class C1)
  rule <k> orderedClass(_,T',((class C1),Ts => (class C2),(class C1),Ts),_) ...</k>
       <className> C1 </className> <extends> C2 </extends>
    if  T' =/=Bool class C1
*/
    
  syntax Exp ::= "l-type" "(" Exp ")"
  rule l-type(X) => X        [:structural:]
  context l-type(_[[HOLE]])
  context l-type([HOLE][_])
  rule l-type(T) => T        [:structural:]

  syntax K ::= "checkDepth" "(" Types "," Type ")"
  rule checkDepth((int,Ts => Ts), (array of T => T))  [:structural:]
  rule checkDepth(.Types,_) => .K                     [:structural:]

  syntax K ::= "bindto" "(" #Id "," Type ")"

  rule <k> bindto(X,T) => existsType(T) ...</k>
       <tenv> Rho:Map (. => X |-> T) </tenv>
       <pass> classPass </pass>
    if notBool(X in keys(Rho))

  rule <k> bindto(X,T) => existsType(T) ~> stmt ...</k>
       <tenv> Rho:Map => Rho[T/X] </tenv>
       <pass> methodPass </pass> 

   syntax K ::=  "tenv" "(" Map ")"

  rule <k> stmt ~> (tenv(Rho) => .) ... </k>
       <tenv> _ => Rho </tenv>                        [:structural:]


  syntax Types ::= "types" "(" Exps ")"    [:prec(1):]
  rule types() => .Types                   [:structural:]
  rule types(X : T, XTs) => T, types(XTs)  [:structural:]


 syntax K ::= "existsType" "(" Type ")" 
  rule existsType(int) => true
  rule existsType(bool) => true
  rule existsType(string) => true
  rule existsType(void) => true
  rule <k> existsType(class C) => true ...</k> <className> C </className>


end module
