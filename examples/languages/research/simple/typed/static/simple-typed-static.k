module SIMPLE-TYPED-STATIC-SYNTAX
  syntax #Id ::= "main"

  syntax Type ::= "int"
                | "bool"
                | "string"
                | "void"
                | "array" "of" Type [:prec(1):]
                | "function" "from" Types "to" Type
                    [:prec(1) latex "{#1}\rightarrow{#2}":]
  syntax Types ::= List{Type,","}

  syntax Decl ::= "var" Exps ";"
                | "function" #Id "(" Exps ")" ":" Type Stmt

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
  syntax Exps ::= List{Exp,","}

  syntax Stmt ::= "{" "}"
                | "{" Stmts "}
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
// the next highlights an error in kompile (see the .k/simple....maude)
                | "whatever"

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts            [:seqstrict prec(100) gather(e E):]

  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X = E1 to E2 do S) = {var X:int=E1; while X <= E2 do {S X=X+1;}}
  macro var E1:Exp, E2:Exp, Es:Exps; = var E1; var E2, Es;
  macro var X:#Id : T:Type = E; = var X : T; X = E;
end module


module SIMPLE-TYPED-STATIC
  imports SIMPLE-TYPED-STATIC-SYNTAX

  syntax Exp ::= Type
  syntax Stmt ::= Type
  syntax KResult ::= Type
  syntax K ::= "1st" | "2nd"

  configuration <T color="red">
                   <k color="green"> $PGM:Stmts </k>
                   <tenv color="cyan"> .Map </tenv>
                   <return> .K </return>
                   <tasks color="blue">
                     <task multiplicity="*">
                       <code> .K </code>
                       <type> .K </type>
                     </task>
                   </tasks>
                   <pass> 1st </pass>
                </T>

  syntax Type ::= "stmt"

// empty list of variable declarations when functions with no arguments
  rule var; => stmt   [: structural:]
  rule var X:#Id : T:Type; => bindto(X,T) ~> stmt
  context var _[[HOLE]] : _;
  rule var X[Ts:Types] : T; => checkDepth(Ts,T) ~> bindto(X,T) ~> stmt

  rule <k> function X(XTs:Exps) : T S:Stmt => 
           bindto (X, function from types(XTs) to T) ~> stmt ...</k>
       <pass> 1st </pass>
       (. => <task> <code> {var XTs; S} </code> <type> T </type> </task>)

//@ Switching to second pass if a main function declared
  rule <k> stmt </k> <tenv>... main |-> function from _ to _ ...</tenv>
       <pass> 1st => 2nd </pass>

//@ When ready in second pass, schedule a next task
  rule <k> stmt => S </k> <pass> 2nd </pass> <return> _ => T </return>
       (<task> <code> S </code> <type> T </type> </task> => .)

// When there is no task left in second pass, do some cleanup
//  rule <k> _:Type </k>
//      (<tasks> .Bag </tasks> <pass> 2nd </pass> <return> _:Type </return> => .)
//         [:structural:]

//@ \section{Expressions}

  rule <k> I:#Int => int ...</k>
  rule <k> B:#Bool => bool ...</k>
  rule <k> Str:#String => string ...</k>
  rule <k> X => T ...</k> <tenv>... X |-> T ...</tenv>
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
  rule _`(_`)(function from Ts to T, Ts) => T
  rule read() => int
  context ([HOLE] => l-type([HOLE])) = _
  rule T=T => T

//@ \section{Statements}

  rule {} => stmt
  rule <k> {Ss:Stmts} => Ss ~> tenv(Rho) ...</k> <tenv> Rho </tenv>
  rule T; => stmt
  rule if bool then stmt else stmt => stmt
  rule while bool do stmt  => stmt
  rule <k> return T; => stmt ...</k> <return> T </return>
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

//@ \section{Auxilliary operations}

  syntax Exp ::= "l-type" "(" Exp ")"
  rule l-type(X) => X        [:structural:]
  context l-type(_[[HOLE]])
  context l-type([HOLE][_])
  rule l-type(T) => T        [:structural:]

  syntax K ::= "bindto" "(" #Id "," Type ")"
             | "checkDepth" "(" Types "," Type ")"
             | "tenv" "(" Map ")"
  rule <k> bindto(X,T) => . ...</k>
       <tenv> Rho:Map => Rho[T / X] </tenv>           [:structural:]
  rule checkDepth((int,Ts => Ts), (array of T => T))  [:structural:]
  rule checkDepth(.Types,_) => .K                     [:structural:]
  rule <k> stmt ~> (tenv(Rho) => .) ... </k>
       <tenv> _ => Rho </tenv>                        [:structural:]

  syntax Types ::= "types" "(" Exps ")"    [:prec(1):]
  rule types() => .Types                   [:structural:]
  rule types(X : T, XTs) => T, types(XTs)  [:structural:]

end module
