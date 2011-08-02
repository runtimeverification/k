
in simple-typed-static-syntax
in ../simple-typed-programs

kmod SIMPLE-TYPED-STATIC-SEMANTICS is including SIMPLE-TYPED-STATIC-DESUGARED-SYNTAX + K 

--- the result of the computation is a list of types
  syntax KResult ::= List{Type}

--- statement value
  syntax Type ::= stmt

--- with types we can make expressions now
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
                </T> 

 
--- first pass: collect function prototypes in gtenv 
  rule <T> <k> S:Stmt ~> (.K => doneGlobals ~> S) </k> 
           (.Bag => <gtenv> .Map </gtenv>) 
       </T>
 
  syntax K ::= doneGlobals  --- to mark when the collection of globals completed

--- global variable declaration
  rule <k> var X:#Id : T:Type ; => stmt <_/k>
       <gtenv> TEnv:Map => TEnv[T / X] </gtenv>

--- function declaration (and definition)
  rule <k> function F:#Id(XTl:List{IdType}) : T S => stmt <_/k>
       <gtenv> TEnv => TEnv[typeList(XTl) -> T / F] </gtenv> [structural] 

--- when we are done with the first pass (doneGlobals mark), replace gtenv by tenv and start typing the bodies of functions
  rule <T> <k> stmt ~> doneGlobals => .K <_/k> 
            ( <gtenv> TEnv </gtenv> 
              =>
              <tenv> TEnv </tenv>
              <return> void </return>
            ) 
       </T> 

--- expressions evaluation
  rule I:#Int => int 
  rule B:#Bool => bool 
  rule <k> X:#Id => T:Type <_/k>
       <tenv_> X |-> T <_/tenv> 
  rule <k> ++ X => int <_/k>
       <tenv_> X |-> int <_/tenv> 
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
  rule T == T => bool 
  rule T != T => bool 
  rule bool and bool => bool 
  rule bool or bool => bool 
  rule not(bool) => bool 
  rule _`[`](T)[int] => T 
  rule sizeOf(T []) => int 

--- variable declaration processing
  rule <k> var X:#Id : T:Type ; => stmt <_/k>
      <tenv> TEnv:Map => TEnv[T / X] </tenv> 
  context var X[[HOLE]] : T ; 
  rule <k> var X[int] : _`[`](T) ; => stmt <_/k>
       <tenv> TEnv => TEnv[_`[`](T) / X] </tenv> 
  rule {} => stmt 

--- the following is used to wrap an enevironment as a computation
  syntax K ::= tenv ( Map )
  rule <k> {S:Stmt} => S ~> tenv(TEnv) <_/k> 
       <tenv> TEnv </tenv> 
  rule <k> stmt ~> (tenv(TEnv) => .K) <_/k> 
          <tenv> _ => TEnv </tenv> 

  rule stmt stmt => stmt 
  rule <k> X = T ; => stmt <_/k> <tenv_> X |-> T <_/tenv>  
  context _[[HOLE]] = _ ; 
  context [HOLE][_] = _ ; 
  rule _`[`](T)[int] = T ; => stmt 
  rule T ; => stmt 
  rule if bool then stmt else stmt => stmt 
  rule while bool do stmt  => stmt 

  rule <k> function F:#Id(XTl:List`{IdType`}) : T S => S ~> tenv(TEnv)<_/k> 
       <tenv> TEnv => TEnv[getList{K}(typeList(XTl)) / getList{K}(idList(XTl))] </tenv> 
       <return> _ => T </return>
  
  rule <k> stmt ~> (tenv(TEnv) => .K)<_/k>
       <tenv> _ => TEnv </tenv> .
  rule _`(_`)(Tl:List`{Type`} -> T,Tl) => T
  rule <k> return(T); => stmt <_/k>
       <return> T </return> 
  rule read() => int 
  rule write(int) ; => stmt   


--- translation of a list of typed names into a list of the corresponding untyped names
  syntax List{Id} ::= idList ( List{IdType} ) 
  macro idList(.List{Bottom}) = .List{Bottom} 
  macro idList(X:#Id : T:Type, XTl:List`{IdType`}) = X, idList(XTl) 

--- translation of a lists of typed names into a list of the corresponding types
  syntax List{Type} ::= typeList ( List{IdType} ) 
  macro typeList(.List{Bottom}) = .List{Bottom} 
  macro typeList(X : T,XTl) = T,typeList(XTl) 

endkm

kmod SIMPLE-TYPED-STATIC is including SIMPLE-TYPED-STATIC-SEMANTICS + SIMPLE-TYPED-PROGRAMS 
  syntax Bag ::= run ( KLabel ) 
  macro run(K:KLabel) = <T>
                           <k> K(.List{K}) </k>
                        </T> 
endkm

