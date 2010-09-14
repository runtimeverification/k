in ../../../../k-prelude.maude
in skool-typed-static-syntax
in ../skool-typed-programs

kmod SKOOL-TYPED-STATIC-SEMANTICS is including SKOOL-TYPED-STATIC-DESUGARED-SYNTAX + K 

--- the result of the computation is a list of types
  syntax KResult ::= List{Type}

--- statement value
  syntax Type ::= stmt

--- with types we can make epressions now
  syntax Exp ::= Type
--- ... and any list of types is a list of expressions
  syntax List{Exp} ::= List{Type} 

--- any type is also a statement
  syntax Stmt ::= Type  

  syntax K ::= Stmts | List{Exp} | List{IdType}

  configuration <T> 
                   <k> .K </k>
                   <tenv> .Map </tenv>
                   <return> stmt </return>
                   <gtenv> .Map </gtenv>
---<SKOOL added>
                     <crntClass> main </crntClass>
                     <pgm>
                           <class*>
                                    <className> Id:Id </className>
                                    <extends> Id:Id </extends>
                                    <stmts> Ss:Stmts </stmts>
                                    <obj> .List </obj>
                                    <tfields> .Map </tfields>
                                    <tmethods> .Map </tmethods>
                                    <methods> .K </methods>
                           </class*>
                           <classRegister> .List{Id} </classRegister> 
                     </pgm>
                     <error> Id:Id </error>
---</SKOOL added>
                </T> 

----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------

--- translation of a list of typed names into a list of the corresponding untyped names
  syntax List{Id} ::= idList ( List{IdType} ) 
  macro idList(.List{Bottom}) = .List{Bottom} 
  macro idList(X:Id : T:Type, XTl:List{IdType}) = X, idList(XTl) 

--- translation of a lists of typed names into a list of the corresponding types
  syntax List{Type} ::= typeList ( List{IdType} ) 
  macro typeList(.List{Bottom}) = .List{Bottom} 
  macro typeList(X : T,XTl) = T,typeList(XTl) 


---<SKOOL added>
--- gettype: returns the type (abstract value) of an object X 
  syntax Type ::= gettype ( Id , List ) [ strict ]

  rule gettype(X, ( ( C:Id :: .) TObj:List )) => gettype(X, TObj ) [structural]
  rule gettype(X, ( ( C :: ( Y:Id |-> T:Type TEnv:Map )) TObj ) )
       => if (X ==Bool Y) then T else gettype(X,  ((C ::  TEnv )TObj)) fi [structural]
  rule gettype(X, .) => void [structural]

--- the next is needed for class types; a class type is a bag of maps "methodName |-> Type"
  syntax MapItem ::= Id |-> Map 

--- typeMap(Ms) returns the map {M |-> type(M) | M in Ms}

  syntax Map ::= typeMap( K )
  rule typeMap(.K) => .Map [structural]
  rule typeMap((method F:Id(XTl:List{IdType}) : T:Type S:Stmt) ~> Ms:K) 
       =>
       (F |-> (typeList(XTl) -> T)) typeMap(Ms)
       [structural]


--- an object evironment layer is a map from the class name to the environm. corresp. to local fields
  syntax ListItem ::= Id :: Map [metadata "latex(renameTo _\\ensuremath{\\mathrel{::}}_)"]

--- the names for the local environment and the global environments for an object
  syntax Id ::= @local | @global

--- successor - ancestor (subclass) relationship
  syntax  Exp ::= Type <: Type [ strict ]

  rule <k> T <: T => bool <_/k>

  rule <k> (type(C1:Id) <: type(C2:Id)) 
           =>
           bool
       <_/k>
       <pgm_>
            <class_>
                     <className> C1 </className>
                     <extends> C2 </extends>
            <_/class>
       <_/pgm>
  rule <k> (type(C1) <: type(C2)) 
           =>
          (type(C11) <: type(C2))
       <_/k>
       <pgm_>
            <class_>
                     <className> C1 </className>
                     <extends> C11:Id </extends>
            <_/class>
       <_/pgm>
       if C1 =/=Bool C2 andBool C1 =/=Bool C2

--- error handling 
  syntax Id ::= error
--- an operation for each leaf cell sort
  op throwError : Map -> Map [ strat (0) ]
  op catch : Map -> Map
--- a rule for each path in the configuration tree
  rule <T_> 
          (. => <error> error </error>)
          <pgm_>
               <class_>
                  <tmethods_> (throwError(Map:Map) => catch(Map)) <_/tmethods>
               <_/class>             
          <_/pgm>
       <_/T>

---</SKOOL added>

--- contexts
  context var X[[HOLE]] : T ; 
  context _[[HOLE]] = _ ; 
  context [HOLE][_] = _ ; 


---<SKOOL modified>

--- first pass: collect classes prototypes in gtenv 
---  rule <T> <k> Ss:Stmts ~> (.K => doneGlobals ~> Ss) </k> 
---           (.Bag => <gtenv> .Map </gtenv> <pgm> .Bag </pgm>) 
---       </T>


--- global variable declaration
  rule <k> var X:Id : T:Type ; => stmt <_/k> 
       <gtenv> TEnv:Map => TEnv[T / X] </gtenv>

  rule <k> var X[int] : _`[`](T) ; => stmt <_/k>
       <gtenv> TEnv => TEnv[_`[`](T) / X] </gtenv> 

---<SKOOL modified>

--- the following rule from Simple are removed (commented)
--- function declaration (and definition)
---  rule <k> function F:Id(XTl:List`{IdType`}) : T S => stmt <_/k> 
---       <gtenv> TEnv => TEnv[typeList(XTl) -> T / F] </gtenv> [structural] 

--- the followings are added


--- a class traversal
  --- the following is used to know when a class preprocessing is finished
  syntax Stmts ::= classProcessing ( Id ) | compType

--- starts a class preprocessing: a new <class> cell is created  and the class name
---   is added in the <classRegister> cell (this is used in the second processing of the class)
  rule <k> class C1:Id extends C2:Id { Ss:Stmts } => classProcessing (C1) <_/k>
       <pgm_> (. => <class_>
                           <className> C1 </className>          
                           <extends> C2 </extends>
                           <stmts> Ss </stmts>
                   <_/class>)
              <classRegister_> . => C1 </classRegister>
       <_/pgm>

--- simple variable member declaration: we have two cases, according to inductive definition of Stmts 
  rule <k> classProcessing(C:Id) <_/k>
       <pgm_>
            <class_>
                     <className> C </className>
                     <stmts> (var X:Id : T:Type ;) Ss => Ss <_/stmts>
                     <tfields> TEnv:Map => TEnv[T/X] </tfields>
            <_/class>
       <_/pgm>
  rule <k> classProcessing(C) <_/k>
       <pgm_>
            <class_>
                     <className> C </className>
                     <stmts> (var X:Id : T:Type ;)  => . <_/stmts>
                     <tfields> TEnv => TEnv[T/X] </tfields>
            <_/class>
       <_/pgm>   

--- array member declaration: we have two cases, similar to simple members
  rule <k> classProcessing(C) <_/k>
       <pgm_>
            <class_>
                     <className> C </className>
                     <stmts> (var X[ N:Nat ] : T[];) Ss => Ss <_/stmts>
                     <tfields> TEnv => TEnv[T[] / X] </tfields>
            <_/class>
       <_/pgm>
  rule <k> classProcessing(C) <_/k>
       <pgm_>
            <class_>
                     <className> C </className>
                     <stmts> (var X[ N:Nat ] : T[];) Ss => Ss <_/stmts>
                     <tfields> TEnv => TEnv[T[] / X] </tfields>
            <_/class>
       <_/pgm>

--- method declaration: two cases again

  rule <k> classProcessing(C) <_/k>
       <pgm_>
            <class_>
                     <className> C </className>
                     <stmts> (method F:Id(XTl:List{IdType}) : T S:Stmt) Ss => Ss <_/stmts>
                     <methods_> .K => method F:Id(XTl:List{IdType}) : T S:Stmt </methods>
            <_/class>
       <_/pgm>

  rule <k> classProcessing(C) <_/k>
       <pgm_>
            <class_>
                     <className> C </className>
                     <stmts> (method F:Id(XTl:List{IdType}) : T S:Stmt)  => . <_/stmts>
                     <methods_> .K => method F:Id(XTl:List{IdType}) : T S:Stmt </methods>
            <_/class>
       <_/pgm>

--- finish preprocessing a class: the empty cell <stmts> is removed 

  rule <k> classProcessing(C) => stmt <_/k>
        <class_>
                <className> C </className>
                ( <stmts> .K </stmts> => .Bag )
       <_/class>


--- when we are done with the first pass (doneGlobals mark),
---    replace gtenv by tenv and start typing the bodies of functions
---  rule <k> doneGlobals => .K <_/k> 
---            ( <gtenv> TEnv </gtenv> 
---              =>
---              <tenv> TEnv </tenv>
---              <return> void </return>
---            ) 

--- when all the classes and global variables are preprocessed,  we may
---    start to compute the class types in the <tmethods> cells and the 
---    instance structure in the <obj> cell

--- we start with a class directly deriving from object; 
---   the fields are wrapped as an environment (list element class-name |-> fields-types)
---   typeMap() returns a multiset of maps meth-name |-> meth-type
---   once processed, a class is removed from the classRegister
  rule <T_>
         <k> stmt => compType </k>
         <pgm_>
              <class_>
                       <className> C </className>
                       <extends> object </extends>
                       (<tfields> FTs:Map </tfields> => .) 
                       <obj> . => (C :: FTs) </obj>
                       <methods> Ms:K </methods>
                       <tmethods> . => typeMap(Ms) </tmethods> 
              <_/class>
              <classRegister_> C => . <_/classRegister>
         <_/pgm>
       <_/T>

--- (induction) base case: similar to the start case
  rule <T_>
         <k> compType </k>
         <pgm_>
              <class_>
                       <className> C </className>
                       <extends> object </extends>
                       (<tfields> FTs:Map </tfields> => .) 
                       <obj> . => (C :: FTs) </obj>
                       <methods> Ms:K </methods>
                       <tmethods> . => typeMap(Ms) </tmethods> 
              <_/class>
              <classRegister_> C => . <_/classRegister>
         <_/pgm>
       <_/T>

--- inductive step: 
---   the instance structure is obtained from the that of the parent by adding current class fields
---   the class type is obtained by merging the methods types of the current class with the type
---   o the parrent; note that the merge operation is partial, it is not defined (error)
---   if there are two methods with the same name and different types (the overloading is not
---   allowed yet)

  rule <T_>
         <k> compType </k>
         <pgm_>
              <class_>
                       <className> C1 </className>
                       <extends> C2 </extends>
                       (<tfields> FTs1:Map </tfields> => .) 
                       <obj> . => (C1 :: FTs1) TObj2 </obj>
                       <methods> Ms:K </methods>
                       <tmethods> . => mergeMethTypes(typeMap(Ms), TC2) </tmethods> 
              <_/class>
              <class_>
                       <className> C2 </className>
                       <obj> TObj2:List </obj>
                       <tmethods> TC2:Map </tmethods> 
              <_/class>
              <classRegister_> C1 => . <_/classRegister>
         <_/pgm>
         <gtenv> TEnv </gtenv>
       <_/T>

--- the definition for the  merge operation
  syntax Map ::= mergeMethTypes ( Map , Map )
  rule mergeMethTypes(TC1:Map, .Map) => TC1
  rule mergeMethTypes(TC1,((M:Id |-> T) TC2))
       =>
       (M |-> T) mergeMethTypes(TC1, TC2)
       if $hasMapping(TC1, M) ==Bool false
       [structural]
  rule mergeMethTypes(((M |-> T1:Type) TC1),((M |-> T2:Type) TC2))
       =>
       (M |-> T1) mergeMethTypes(TC1, TC2)
       if T1 ==Bool T2
       [structural]

--- throws  an error when two methods with the same name but different types are met
  rule mergeMethTypes(((M |-> T1:Type) TC1),((M |-> T2:Type) TC2))
       =>
       throwError(mergeMethTypes(((M |-> T1:Type) TC1),((M |-> T2:Type) TC2)))
       if T1 =/=Bool T2
       [structural]
--- 

--- finishing the class type computation (the <classRegister> cell is empty)
---   the <classRegister> cell is removed and added the other cells needed for the second processing

  rule <T_>
         <k> compType => stmt </k>
         ( .Bag => (<crntClass> object </crntClass>
                    <tenv> .Map </tenv>
                    <return> stmt </return>
                   )
         )
         <pgm_> <classRegister> .List{Id} </classRegister> => .Bag <_/pgm>
         <gtenv> TEnv  </gtenv>
       <_/T> 


---</SKOOL modified>

--- expression evaluation

  rule I:Int => int 
  rule B:Bool => bool 

---<SKOOL modified>
---  rule <k> X:Id => T:Type <_/k>
---       <tenv_> X |-> T <_/tenv> 

--- the type of variable name is computed with the gettype function, which 
---   searches between local variables, variable members, and global variables
  rule <k> X:Id => gettype(X, ((@local :: TEnv) TObj (@global :: GTEnv))) <_/k>
       <crntClass> C:Id </crntClass>
       <pgm_>
            <class_>
                     <className> C </className>
                     <obj> TObj:List </obj>
            <_/class>
       <_/pgm>
       <tenv> TEnv:Map </tenv>
       <gtenv> GTEnv:Map </gtenv>

---  rule <k> ++ X => int <_/k>
---       <tenv_> X |-> int <_/tenv> 


--- the following should be conditional (see Issue 58)
  rule <k> ++ X => gettype(X, ((@local :: TEnv) TObj (@global :: GTEnv))) <_/k>
       <crntClass> C </crntClass>
       <pgm_>
            <class_>
                     <className> C </className>
                     <obj> TObj </obj>
            <_/class>
       <_/pgm>
       <tenv> TEnv </tenv>
       <gtenv> GTEnv </gtenv>

--- function call
--- rule _`(_`)(Tl:List`{Type`} -> T,Tl) => T 
--- method call
  rule <k> _._`(_`)(type(C), F:Id, Tl) => T <_/k>
       <pgm_>
            <class_>
                     <className> C </className>
                     <tmethods_> F |-> Tl2:List{Type} -> T <_/tmethods>
            <_/class>
       <_/pgm>

---</SKOOL modified>

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
  rule T:Type == T => bool 
  rule T != T => bool 
  rule bool and bool => bool 
  rule bool or bool => bool 
  rule not(bool) => bool 
  rule _`[`](T)[int] => T 
  rule sizeOf(T []) => int 
  rule read() => int 

---<SKOOL added>

--- new operator

  rule new C(Tl:List{Type}) => type(C) 

--- instanceOf is reduced to subtype relation
  rule <k> _instanceOf_(T, C) => T <: type(C) <_/k> 

---</SKOOL added>

--- local variables declarations

  rule <k> var X:Id : T:Type ; => stmt <_/k>
      <tenv> TEnv:Map => TEnv[T / X] </tenv> 
  rule <k> var X[int] : _`[`](T) ; => stmt <_/k>
       <tenv> TEnv => TEnv[_`[`](T) / X] </tenv> 

--- bloc instruction
  rule {} => stmt 

--- the following is used to wrap an enevironment as a computation
  syntax K ::= tenv ( Map )
  rule <k> {S:Stmt} => S ~> tenv(TEnv) <_/k> 
       <tenv> TEnv </tenv> 
  rule <k> stmt ~> (tenv(TEnv) => .K) <_/k> 
          <tenv> _ => TEnv </tenv> 

--- idempotence of stmt
  rule stmt stmt => stmt 

--- assignment
---<SKOOL modified>
---  rule <k> X = T ; => stmt <_/k>
---       <tenv_> X |-> T <_/tenv>  

--- the assignment is reduced to subtype relationship

  rule (T1 = T2 ;) => (T2 <: T1) ; 
  rule (_`[`](T1:Type)[int] = T2:Type ;) => (T1 <: T2) ; 
---</SKOOL modified>

  rule T ; => stmt 
  rule if bool then stmt else stmt => stmt 
  rule while bool do stmt  => stmt 

---<SKOOL modified>
---  rule <k> function F:Id(XTl:List`{IdType`}) : T S => S ~> tenv(TEnv)<_/k> 
---       <tenv> TEnv => TEnv[getList{K}(typeList(XTl)) / getList{K}(idList(XTl))] </tenv> 
---       <return> _ => T </return>

--- method processing

  rule <k> stmt => S ~> tenv(TEnv) </k>
       <crntClass> _ => C1 </crntClass>
       <pgm_>  
            <class_>
                    <className> C1:Id </className>
                    <methods> (method F:Id(XTl:List{IdType}) : T S:Stmt) => .  <_/methods>
            <_/class>
       <_/pgm>
       <return> _ => T </return>
       <tenv> TEnv => .Map[getList{K}(typeList(XTl)) / getList{K}(idList(XTl))] </tenv>

  rule <k> stmt </k>
       <pgm_>  
            <class_>
                    (<methods> .K  <_/methods>) => .Bag
            <_/class>
       <_/pgm>

---</SKOOL modified>

  rule <k> return(T); => stmt <_/k>
       <return> T </return> 

  rule write(int) ; => stmt   

endkm

kmod SKOOL-TYPED-STATIC is including SKOOL-TYPED-STATIC-SEMANTICS + SKOOL-TYPED-PROGRAMS 
  syntax Bag ::= run ( KLabel ) 
  macro run(K:KLabel) = <T>
                           <k> K(.List{K}) </k>
                           <gtenv> .Map </gtenv>
                           <pgm> .Bag <classRegister> .List{Id} </classRegister> </pgm>
                        </T> 
endkm

