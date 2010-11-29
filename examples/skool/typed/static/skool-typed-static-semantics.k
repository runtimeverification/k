--------------------------------------------
--- SKOOL-TYPED-DYNAMIC-SEMANTICS module ---
--------------------------------------------

kmod SKOOL-TYPED-STATIC-SEMANTICS is including SKOOL-TYPED-STATIC-DESUGARED-SYNTAX + K 

--- both expression and statements can evaluate to types
  syntax Type ::= stmt | decl | correct

  syntax Exp ::= Type
  syntax List{Exp} ::= List{Type} 
  syntax Stmt ::= Type

--- We have to subsort all the syntactic categories to K, and the lists of types
--- to KResult.  Recall that the second argument of a method application is a list
--- of expressions, so that becomes a result when it becomes a list of values

  syntax K ::= Stmts | List{Exp} | List{Type} | List{VarType} | List{Top}
  syntax KResult ::= List{Type} 

  configuration <T> 
                     <k> .K </k>
                     <tenv> .Map </tenv>
                     <return> stmt </return>
---<SKOOL added>
                     <crntClass> .K </crntClass>
                     <classes>
                           <class*> 
                                    <className> Id:Id </className>
                                    <extends?> Id:Id </extends?>
                                    <ctenv> .Map </ctenv>
                           </class*>
                     </classes>
                     <pass> start </pass>
                     <pgm> .K </pgm>
---</SKOOL added>
                </T>


  syntax Pass ::= start | global | classes | methods | end
  syntax K ::= Pass

-------------------------------
--- declarations processing ---
-------------------------------

---  start the first pass through the program to collect declarations

  rule <k> .K => Pgm:Stmts </k> <pgm> Pgm </pgm> <pass> start => global </pass>

--- variable declaration; in the preprocessing phase only the global variables are processed 
--- this rule is also used to process the local variables of a function
---   as a part of the function evaluation 

  rule I:Int => int 
  rule B:Bool => bool 
  
  rule [decl-variable]: <k> var X:Id : Tp:Type ; => decl <_/k> 
       <tenv> TEnv:Map => TEnv[Tp / X] </tenv> <pass> Pass </pass>
       if Pass =/=Bool global

--- If an array is declared, then calculate its size; 

  context var X:Id[[HOLE]] : Tp ;
  rule [decl-array]: <k> var X[int] : _`[`](Tp) ; => decl <_/k> 
       <tenv> TEnv => TEnv[ _`[`](Tp)/X] </tenv>  <pass> Pass:Pass </pass>
       if Pass =/=Bool global

  rule (sizeOf(_`[`](Tp)) => int)   

---<SKOOL modified>

  rule [decl-method]: <k> method F:Id(XTl:List{VarType}) : Tp S:Stmt => decl <_/k> 
       <tenv_> . => F |-> ((typeList(XTl)->Tp)) <_/tenv> 
       <pass> classes </pass> 

--- the followings are added

--- a class traversal
  rule [decl-class]: 
       <k> class C1:Id extends C2:Id { Ss:Stmts } => Ss ~> env(TEnv) <_/k>
       (. => <class_>
                           <className> C1 </className>          
                           <extends> C2 </extends>
                   <_/class>)
       <crntClass> _ => class C1 </crntClass>
       <tenv> TEnv </tenv> 
       <pass> global => classes </pass>

  syntax K ::= env ( Map ) 

  rule <k> decl ~> (env(TEnv) => .) <_/k>
       <tenv> TEnv':Map => TEnv </tenv>
       <crntClass> class C1 </crntClass>
       <className> C1 </className>
       <ctenv> _ => TEnv' </ctenv>
       <pass> classes => global </pass>
      
       
--- when we are done with the first pass (preprocessing), i.e., the computation and gtenv are empty, 
  rule [pass-two]: <k> decl => Pgm </k>
       <tenv> TEnv => . </tenv>
       (. => 
        <class_> <className> object </className> <tenv> TEnv </tenv> <_/class>)
      <pgm> Pgm </pgm>
      <pass> global => methods </pass>

  rule [done]: <k> Tp => correct </k>
       <pass> methods => end </pass>


--- At the second pass, we need to type each method of each class

  rule [type-class]: 
       <k> class C1:Id extends C2:Id { Ss } => Ss <_/k>
       <crntClass> _ => class C1 </crntClass>
       <pass> methods </pass>

  rule [type-method]: 
       <k> (method F:Id(XTl:List{VarType}) : Tp S:Stmt => S) <_/k> 
       <tenv> _ => getList{K}(idList(XTl)) |-> getList{K}(typeList(XTl)) </tenv> 
       <return> _ => Tp </return> <pass> methods </pass>

  


---</SKOOL modified>

-------------------
--- Expressions ---
-------------------

--- variable lookup

  rule [lookup-var]: <k> X:Id => Tp <_/k>  
       <tenv_> X |-> Tp <_/tenv>

---<SKOOL extension>
  --- if an id is not in the local environment assume it's a field 
  --- static lookup for fields
  rule [lookup-field]: <k> X:Id => _._(this,X) <_/k>
       <tenv> TEnv:Map </tenv>
       if notBool(X in keys(TEnv)) [structural]

  rule [this]: <k> this => Tp <_/k>  
       <crntClass> Tp </crntClass>

  rule [super]: <k> super => class C2 <_/k>
       <crntClass> class C1 </crntClass>
       <className> C1 </className> 
       <extends> C2 </extends>

  --- looking up in object
  rule <k> _._(class C,X) => Tp <_/k>
      <className> C </className> <ctenv_> X |-> Tp <_/ctenv>
 
  rule <k> _._(class (C1 => C2),X) <_/k>
      <className> C1 </className> <extends> C2 </extends> <ctenv> TEnv </ctenv>
      if notBool(X in keys(TEnv)) [structural]

---</SKOOL extension>

--- arithmetic expressions

  syntax K ::= ++ K [ditto]

  rule [pre-inc]: ++int => int 
  rule int + int => int
  rule _-_(int,int) => int
  rule int * int => int
  rule int / int => int
  rule int % int => int
  rule - int => int
  rule int < int => bool
  rule int <= int => bool
  rule int > int => bool
  rule int >= int => bool
  rule Tp == Tp => bool
  rule Tp != Tp => bool
  rule bool and bool => bool
  rule bool or bool => bool
  rule not(bool) => bool

--- array component value:

  rule [array-indexing]: _`[`](Tp)[int] => Tp

--- read expression

  rule [input]: read() => int

---<SKOOL added>
--- new operator
---   the semantics of the new operator consists of two actions: memory allocation for the new object
---   and the execution of the statements included in the constructor
---   the current class, environment and object are stored on the stack

  rule [new-object]: (new_`(_`)(C:Id, Tpl)) => _`(_`)(_._(class C,C), Tpl)


--- instanceOf operator

  rule [instanceOf]: <k> _instanceOf_(class C1, C2) => bool<_/k>
       <classes> Cls:Bag </classes>
       if subtype(class C1,class C2,Cls)

--- as operator

  rule [as]: <k> _as_(class C1, C2) => class C2<_/k>
       <classes> Cls:Bag </classes>
       if subtype(class C1,class C2,Cls)

---</SKOOL added>

---------------------
--- method call ---
---------------------

---<SKOOL modified>


 rule <k> _`(_`)((Tpl:List{Type}->Tp),Tpl':List{Type}) => Tp <_/k>
       <classes> Cls </classes>
    if subtype(Tpl', Tpl, Cls)

  rule <k> return(Tp);  => stmt <_/k>
       <return> Tp' </return>
       <classes> Cls </classes>
    if subtype(Tp, Tp', Cls)

---</SKOOL modified>

------------------------------
--- instruction processing ---
------------------------------
  rule {} => stmt
  rule {stmt} => stmt
  rule stmt stmt => stmt
  rule stmt decl => stmt
  rule decl stmt => stmt
  rule decl decl => decl

  context ([HOLE]=_;) if (l-value([HOLE]))

  syntax Bool ::= l-value ( K )

  rule l-value(X) => true [structural]
  rule l-value(_._(_,_)) => true [structural]
  rule l-value(_`[_`](_,_)) => true [structural]

  rule <k> Tp=Tp'; => stmt <_/k> 
       <classes> Cls </classes>
    if subtype(Tp', Tp,Cls)

  rule Tp; => stmt 
  rule if bool then stmt else stmt => stmt
  rule while bool do stmt  => stmt
  rule write(int,Tpl); => write(Tpl);
  rule write(.List{Bottom}); => stmt 


----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------


---</SKOOL added>
  syntax List{Id} ::= idList ( List{VarType} ) 
  macro idList(.List{Bottom}) = .List{Bottom} 
  macro idList(X:Id : Tp, XTl:List{VarType}) = X, idList(XTl) 

--- translation of a lists of typed names into a list of the corresponding types
  syntax List{Type} ::= typeList ( List{VarType} ) 
  macro typeList(.List{Bottom}) = .List{Bottom} 
  macro typeList(X : Tp,XTl) = Tp,typeList(XTl) 

---<SKOOL added>

--- subtype relationship

  syntax Bool ::= subtype ( List{Type} , List{Type} , Bag )  [latex "{#1}\mathrel{\leq_{{#3}}}{#2}"]
  macro subtype((Tp1:Type,Tp1':Type,Tpl1:List{Type}),(Tp:Type,Tp':Type,Tpl:List{Type}), Cls) = subtype(Tp1,Tp, Cls) andBool subtype((Tp1',Tpl1), (Tp',Tpl), Cls)
  macro subtype(.List{Bottom},.List{Bottom},_) = true 
  macro subtype(Tp, Tp, _) = true
  macro subtype(class object, class C, _) = C ==Bool object
  rule subtype(class (C1 => C2), class C, (Cls <class_> <className> C1 </className> <extends> C2 </extends> </class>)) 
      [structural]
  macro subtype(int, class _,_) = false 
  macro subtype(bool, class _,_) = false 
  macro subtype(void, class _,_) = false 
  macro subtype(class _, int,_) = false 
  macro subtype(class _, bool,_) = false 
  macro subtype(class _, void,_) = false 

---</SKOOL added>


endkm


