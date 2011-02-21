--------------------------------------------
--- SKOOL-TYPED-DYNAMIC-SEMANTICS module ---
--------------------------------------------

kmod SKOOL-TYPED-STATIC-SEMANTICS is including SKOOL-TYPED-STATIC-DESUGARED-SYNTAX + K 

--- both expression and statements can evaluate to types
  syntax Type ::= stmt | decl | correct

  syntax Exp ::= Type  
  syntax Stmt ::= Type
  syntax List{Exp} ::= List{Type} 

--- We have to subsort all the syntactic categories to K, and the lists of types
--- to KResult.  Recall that the second argument of a method application is a list
--- of expressions, so that becomes a result when it becomes a list of values

  syntax KResult ::= List{Type} 

---------------------
--- Configuration ---
---------------------

  configuration <T> 
                     <k> .K </k>
                     <tenv> .Map </tenv>
                     <return> stmt </return>
                     <crntClass> .K </crntClass>
                     <classes>
                           <class multiplicity="*"> 
                                    <className> Id:Id </className>
                                    <extends multiplicity="?"> Id:Id </extends>
                                    <ctenv> .Map </ctenv>
                           </class>
                     </classes>
                     <pass> start </pass>
                     <pgm> .K </pgm>
                </T>


  syntax Pass ::= start | global | classes | methods | end
  syntax K ::= Pass



---  start the first pass through the program to collect declarations

  rule <k> .K => Pgm:Stmts </k> <pgm> Pgm </pgm> <pass> start => global </pass>

-------------------------------
--- declarations processing ---
-------------------------------

--- variable declaration; forbidden at the global level
--- this rule is to process both field declarations and 
--- local variables of a function

  rule [decl-variable]: <k> var X:Id : Tp:Type ; => decl <_/k> 
       <tenv> TEnv:Map => TEnv[Tp / X] </tenv> <pass> Pass </pass>
       if Pass =/=Bool global

--- Array declaration
  context var X:Id[[HOLE]] : Tp ;
  rule [decl-array]: <k> var X[int] : _`[`](Tp) ; => decl <_/k> 
       <tenv> TEnv => TEnv[ _`[`](Tp)/X] </tenv>  <pass> Pass:Pass </pass>
       if Pass =/=Bool global

--- when processing class declarations, disregard initializers
  rule [decl-initializer]: <k> var X : Tp = E:Exp ; => var X : Tp; <_/k> 
                      <pass> classes </pass>

--- Method declaration, only inside a class declaration
--- we add to the typing environment the type of the method.
  rule [decl-method]: <k> method F:Id(XTl:List{VarType}) : Tp S:Stmt => decl <_/k> 
       <tenv_> . => F |-> ((typeList(XTl)->Tp)) <_/tenv> 
       <pass> classes </pass> 

--- Class declaration
--- we create a class prototype where the field and method declarations will 
--- be stored.
  rule [decl-class]: 
       <k> class C1:Id extends C2:Id { Ss:Stmts } => Ss ~> global <_/k>
       (. => <class_>
                           <className> C1 </className>          
                           <extends> C2 </extends>
                   <_/class>)
       <crntClass> _ => class C1 </crntClass>
       <pass> global => classes </pass>

--- Return to the global pass after the class declaration was typed
--- at the same time, store the class environment.
  rule <k> decl ~> (global => .) <_/k>
       <tenv> TEnv => . </tenv>
       <crntClass> class C1 </crntClass>
       <className> C1 </className>
       <ctenv> _ => TEnv </ctenv>
       <pass> classes => global </pass>
      
       
--- when we are done with the first pass (preprocessing), the computation 
--- should consists of a decl; we now start typing the methods. 
  rule [pass-two]: <k> decl => Pgm </k>
       (. => 
        <class_> <className> object </className> <_/class>)
      <pgm> Pgm </pgm>
      <pass> global => methods </pass>

--- Once all methods have been typed, we deem the program correct.
  rule [done]: <k> Tp => correct </k>
       <pass> methods => end </pass>


--- initializers are typed together with the methods
  rule [type-initializer]:  <k> var X : Tp = E; => __(var X : Tp;,X = E;) <_/k> 
                      <pass> methods </pass>

--- Typing method bodies: similar to function call
  rule [type-method]: 
       <k> (method F:Id(XTl:List{VarType}) : Tp S:Stmt => S) <_/k> 
       <tenv> _ => getList{K}(idList(XTl)) |-> getList{K}(typeList(XTl)) </tenv> 
       <return> _ => Tp </return> <pass> methods </pass>

  
--- Typing each method in the class.
  rule [type-class]: 
       <k> class C1:Id extends C2:Id { Ss } => Ss <_/k>
       <crntClass> _ => class C1 </crntClass>
       <pass> methods </pass>


-------------------
--- Expressions ---
-------------------

--- typing constants
  rule I:Int => int 
  rule B:Bool => bool 

--- Local variable lookup
--- If X is in the local environment, then it is a local variable, not a field.
  rule [lookup-var]: <k> X:Id => Tp <_/k>  
       <tenv_> X |-> Tp <_/tenv>

--- Field lookup
--- If X is not in the local environment, then assume that it's a field of "this".
--- General object lookup defined at its place below (we follow the order in the SKOOL syntax).
  rule [lookup-field]: <k> X:Id => _._(this,X) <_/k>
       <tenv> TEnv:Map </tenv>
       if notBool(X in keys(TEnv)) [structural]

--- Increment
--- Only type argument if it is an l-value; we don't want to increment 5
  context (++[HOLE]) if (l-value([HOLE]))
  rule [increment]: ++int => int 


--- Arithmetic Operators
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

--- Array lookup and sizeof:  check that we have an array 
--- evaluate to corresponding type
  rule [array-indexing]: _`[`](Tp)[int] => Tp
  rule (sizeOf(_`[`](Tp)) => int)   

--- Method Call: check that argument types are compatible 
 rule <k> _`(_`)((Tpl:List{Type}->Tp),Tpl':List{Type}) => Tp <_/k>
       <classes> Cls </classes>
    if subtype(Tpl', Tpl, Cls)

--- Return: check that return type is compatible
  rule <k> return(Tp);  => stmt <_/k>
       <return> Tp' </return>
       <classes> Cls </classes>
    if subtype(Tp, Tp', Cls)


--- Read expression: currently only integers can be read
  rule [input]: read() => int

--- new operator
---  to type new we only need to check that the class constructor can be
---  called with arguments of the given type. 
  rule [new-object]: (new_`(_`)(C:Id, Tpl)) => _`(_`)(_._(class C,C), Tpl)


--- this types to the current class
  rule [this]: <k> this => Tp <_/k>  
       <crntClass> Tp </crntClass>

--- super types to the parent class.
--- Note that for typing concerns super can be considered as an object
  rule [super]: <k> super => class C2 <_/k>
       <crntClass> class C1 </crntClass>
       <className> C1 </className> 
       <extends> C2 </extends>

--- Object member access
------------------------

--- Case 1: member declared in current class
  rule <k> _._(class C,X) => Tp <_/k>
      <className> C </className> <ctenv_> X |-> Tp <_/ctenv>
 
--- Case 2: member not declared in current class; check parent class
  rule <k> _._(class (C1 => C2),X) <_/k>
      <className> C1 </className> <extends> C2 </extends> <ctenv> TEnv </ctenv>
      if notBool(X in keys(TEnv)) [structural]

--- instanceOf and casting
--------------------------
--- As it is hard to check statically whether casting is always safe,
--- we here only check that the types are compatible.

--- instanceOf
  rule [instanceOf]: <k> _instanceOf_(class C1, C2) => bool<_/k>
       <classes> Cls:Bag </classes>
       if subtype(class C1,class C2,Cls) orBool subtype(class C2,class C1,Cls)

--- Casting
  rule [as]: <k> cast_to_(Tp, Tp') => Tp'<_/k>
       <classes> Cls:Bag </classes>
       if subtype(Tp,Tp',Cls) orBool subtype(Tp',Tp,Cls)

------------------
--- Statements ---
------------------
  rule {} => stmt
  rule {stmt} => stmt

--- Assignment
--- Only type left hand side if it is an l-value; we don't want to assign to 5
  context ([HOLE]=_;) if (l-value([HOLE]))

  rule <k> Tp=Tp'; => stmt <_/k> 
       <classes> Cls </classes>
    if subtype(Tp', Tp,Cls)

--- Expression statement
  rule Tp; => stmt 

--- Conditional
  rule if bool then stmt else stmt => stmt

--- While
  rule while bool do stmt  => stmt

--- Write:  we check each argument is a basic type
  rule write(int,Tpl); => write(Tpl);
  rule write(bool,Tpl); => write(Tpl);
  rule write(.List{Bottom}); => stmt 

--- Sequential composition:  we want to check whether a sequence consists 
--- only of declarations (i.e., there are no statements in a class body)
  rule stmt stmt => stmt
  rule stmt decl => stmt
  rule decl stmt => stmt
  rule decl decl => decl

----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------

--- l-value predicate
  syntax Bool ::= l-value ( K )
  rule l-value(X) => true [structural]
  rule l-value(_._(_,_)) => true [structural]
  rule l-value(_`[_`](_,_)) => true [structural]

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



--- translation of a lists of typed names into a list of the corresponding Ids
  syntax List{Id} ::= idList ( List{VarType} ) 
  macro idList(.List{Bottom}) = .List{Bottom} 
  macro idList(X:Id : Tp, XTl:List{VarType}) = X, idList(XTl) 

--- translation of a lists of typed names into a list of the corresponding types
  syntax List{Type} ::= typeList ( List{VarType} ) 
  macro typeList(.List{Bottom}) = .List{Bottom} 
  macro typeList(X : Tp,XTl) = Tp,typeList(XTl) 

endkm
