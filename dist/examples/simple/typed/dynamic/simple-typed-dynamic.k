module SIMPLE-TYPED-DYNAMIC-SYNTAX

/*@ \section{Syntax}
The syntax of typed SIMPLE extends that of untyped SIMPLE with support
for declaring types to variables and functions.  The syntax below is identical
to that of the static semantics of typed SIMPLE.  However, the \K
strictness attributes are like those of the untyped SIMPLE, to capture
the desired evaluation strategies of the various language constructs .  */

//@ \subsection{Types}

  syntax Type ::= "void" | "int" | "bool" | "string"
                | Type "[" "]"
                > Types "->" Type
                | "(" Type ")"             [bracket]

  syntax Types ::= List{Type,","}

//@ \subsection{Declarations}

  syntax Param ::= Type Id
  syntax Params ::= List{Param,","}

  syntax Decl ::= Type Exps ";"
                | Type Id "(" Params ")" Block

//@ \subsection{Expressions}

  syntax Exp ::= Int | Bool | String | Id
               | "(" Exp ")"             [bracket]
               | "++" Exp
               > Exp "[" Exps "]"        [strict]
               > Exp "(" Exps ")"        [strict]
               | "-" Exp                 [strict]
               | "sizeOf" "(" Exp ")"    [strict]
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
               > "!" Exp                 [strict]
               > left:
                 Exp "&&" Exp            [strict(1), left]
               | Exp "||" Exp            [strict(1), left]
               > "spawn" Block
               > Exp "=" Exp             [strict(2), right]

  syntax Exps ::= List{Exp,","}          [strict, hybrid]

//@ \subsection{Statements}

  syntax Block ::= "{" "}"
                | "{" Stmts "}"

  syntax Stmt ::= Decl | Block
                | Exp ";"                               [strict]
                | "if" "(" Exp ")" Block "else" Block   [avoid, strict(1)]
                | "if" "(" Exp ")" Block
                | "while" "(" Exp ")" Block
        	| "for" "(" Stmt Exp ";" Exp ")" Block
                | "return" Exp ";"                      [strict]
                | "return" ";"
                | "print" "(" Exps ")" ";"              [strict]
                | "try" Block "catch" "(" Param ")" Block
        	| "throw" Exp ";"                       [strict]
                | "join" Exp ";"                        [strict]
                | "acquire" Exp ";"                     [strict]
                | "release" Exp ";"                     [strict]
                | "rendezvous" Exp ";"                  [strict]

  syntax Stmts ::= Stmt
                 | Stmts Stmts                          [right]

//@ We use the same desugaring macros like in typed SIMPLE

  rule if (E) S => if (E) S else {}                                 [macro]
  rule for(Start Cond; Step) {S} => {Start while (Cond) {S Step;}}  [macro]
  rule T:Type E1:Exp, E2:Exp, Es:Exps; => T E1; T E2, Es;           [macro]
  rule T:Type X:Id = E; => T X; X = E;                              [macro]

  syntax Id ::= "main"
endmodule


module SIMPLE-TYPED-DYNAMIC
  imports SIMPLE-TYPED-DYNAMIC-SYNTAX

  syntax Val ::= Int | Bool | String
               | array(Type,Int,Int)
               | lambda(Type,Params,Stmts)
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

//@ \section{Configuration}

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> ($PGM:Stmts ~> execute) </k>
                      <br/>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
                        <return color="LimeGreen"> void </return> //return type
                       </control>
                      <br/>
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Map </holds>
                      <id color="pink"> 0 </id>
                    </thread>
                  </threads>
                  <br/>
                  <genv color="pink"> .Map </genv>
                  <store color="white"> .Map </store>
                  <busy color="cyan">.Set</busy>
                  <terminated color="red"> .Set </terminated>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="brown" stream="stdout"> .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
                </T>

//@ \section{Declarations and Initialization}

//@ \subsection{Variable Declaration}

  syntax K ::= undefined(Type)  [latex(\bot_{#1})]

  rule <k> T:Type X:Id; => . ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> undefined(T) ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>

//@ \subsection{Array Declaration}

  rule <k> T:Type X:Id[N:Int]; => . ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> array(T, L +Int 1, N)
                       (L +Int 1)...(L +Int N) |-> undefined(T) ...</store>
       <nextLoc> L:Int => L +Int 1 +Int N </nextLoc>

  context _:Type _[HOLE];

  syntax Id ::= "$1" | "$2"
  rule T:Type X:Id[N1:Int, N2:Int, Vs:Vals];
    => T[]<Vs> X[N1];
       {
         T[][]<Vs> $1=X;
         for(int $2=0; $2 <= N1 - 1; ++$2) {
           T X[N2,Vs];
           $1[$2] = X;
         }
       }
    [structural]
  syntax Type ::= Type "<" Vals ">"  [function]
  rule T:Type<_,Vs:Vals> => T[]<Vs>
  rule T:Type<.Vals> => T

//@ \subsection{Function declaration}

  rule <k> T:Type F:Id(Ps:Params) B => . ...</k>
       <env> Env => Env[L/F] </env>
       <store>... . => L |-> lambda(T, Ps, B) ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>

  syntax K ::= "execute"
  rule <k> execute => main(.Exps); </k>
       <env> Env </env>
       <genv> . => Env </genv>
    [structural]

//@ \section{Expressions}

  rule <k> X:Id => V ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V ...</store>  [transition]

//@ \subsection{Variable/Array increment}

  context ++(HOLE => lvalue(HOLE))
  rule <k> ++loc(L) => I +Int 1 ...</k>
       <store>... L |-> (I => I +Int 1) ...</store>  [transition]

//@ \subsection{Arithmetic operators}

  rule I1:Int + I2:Int => I1 +Int I2
  rule Str1:String + Str2:String => Str1 +String Str2
  rule I1:Int - I2:Int => I1 -Int I2
  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=K 0
  rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=K 0
  rule - I:Int => 0 -Int I
  rule I1:Int < I2:Int => I1 <Int I2
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule I1:Int > I2:Int => I1 >Int I2
  rule I1:Int >= I2:Int => I1 >=Int I2
  rule V1:Val == V2:Val => V1 ==K V2
  rule V1:Val != V2:Val => V1 =/=K V2
  rule ! T:Bool => notBool(T)
  rule true  && E => E
  rule false && _ => false
  rule true  || _ => true
  rule false || E => E

//@ \subsection{Array lookup}

// It would be nice to get rid of the next two anywhere rules!
// Besides the top level of the computation, they are only needed inside the
// lvalue wrapper.  Maybe we need some additional notation for this?

  rule V:Val[N1:Int, N2:Int, Vs:Vals] => V[N1][N2, Vs]
    [structural, anywhere]

  rule array(_:Type, L:Int, M:Int)[N:Int] => lookup(L +Int N)
    when N >=Int 0 andBool N <Int M
    [structural, anywhere]

  syntax K ::= lookup(Int)
  rule <k> lookup(L) => V ...</k> <store>... L |-> V ...</store>
    [transition]

//@ \subsection{Size of an array}

  rule sizeOf(array(_,_,N)) => N

//@ \subsection{Function call}

  syntax ListItem ::=  (Type,Map,K,Bag)

  rule <k> lambda(T,Ps,B)(Vs:Vals) ~> K => bind(Ps,Vs) ~> B ~> return; </k>
       <control>
         <fstack> . => (T',Env,K,C) ...</fstack>
         <return> T' => T </return>
         C
       </control>
       <env> Env => GEnv </env>
       <genv> GEnv </genv>

  rule <k> return V:Val; ~> _ => V ~> K </k>
       <control>
         <fstack> (T',Env,K,C) => . ...</fstack>
         <return> T => T' </return>
         (_ => C)
       </control>
       <env> _ => Env </env>
    when type(V) ==K T

  syntax Val ::= nothing(Type)
  rule <k> return; => return nothing(T); ...</k> <return> T </return>
    [structural]

  syntax K ::= bind(Params,Vals)

  rule <k> bind((T:Type X:Id,Ps:Params => Ps),(V:Val,Vs:Vals => Vs)) ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> V ...</store>
       <nextLoc> L => L:Int +Int 1 </nextLoc>
    when type(V) ==K T  [structural]

  rule bind(.Params, .Vals) => .  [structural]

//@ \subsection{Read}

  rule <k> read() => I ...</k> <in> ListItem(I:Int) => . ...</in>
    [transition]

//@ \subsection{Assignment}

  context (HOLE => lvalue(HOLE)) = _

  rule <k> loc(L) = V:Val => V ...</k> <store>... L |-> (V' => V) ...</store>
    when type(V) ==K type(V')
    [transition]

//@ \section{Statements}

//@ \subsection{Blocks}

  rule {} => .  [structural]
  rule <k> { Ss:Stmts } => Ss ~> env(Env) ...</k>  <env> Env </env>
    [structural]

//@ Environment recovery

  syntax K ::= env(Map)
  rule <k> env(Env) => . ...</k>  <env> _ => Env </env>  [structural]
  rule (env(_) => .) ~> env(_)  [structural]

//@ \subsection{Sequential composition}

  rule S1:Stmts S2:Stmts => S1 ~> S2  [structural]

//@ \subsection{Expression statements}

  rule _:Val; => .

//@ \subsection{Conditional}

  rule if ( true) S else _ => S
  rule if (false) _ else S => S

//@ \subsection{While loop}

  rule while (E) S => if (E) {S while(E)S}  [structural]

//@ \subsection{Print}

  rule <k> print(V:Val, Es => Es); ...</k> <out>... . => ListItem(V) </out>
    when type(V) ==K int orBool type(V) ==K string
    [transition]
  rule print(.Vals); => .  [structural]

//@ \subsection{Exceptions}

 syntax ListItem ::= (Param,Stmt,K,Map,Bag)

  syntax K ::= "popx"

  rule <k> (try B catch(P) {Ss} => B ~> popx) ~> K </k>
       <control>
         <xstack> . => (P, Ss, K, Env, C) ...</xstack>
         C
       </control>
       <env> Env </env>

  rule <k> popx => . ...</k>
       <xstack> _:ListItem => . ...</xstack>

  rule <k> throw V:Val; ~> _ => { T X = V; Ss } ~> K </k>
       <control>
         <xstack> (T:Type X:Id, Ss, K, Env, C) => . ...</xstack>
         (_ => C)
       </control>
       <env> _ => Env </env>

//@ \subsection{Threads}

//@ \subsubsection{Thread creation}

   rule <thread>...
          <k> spawn S => T ...</k>
          <env> Env </env>
        ...</thread>
        (. => <thread>...
                <k> S </k>
                <env> Env </env>
                <id> T </id>
              ...</thread>)
     when fresh(T:Int)

//@ \subsubsection{Thread termination}

   rule (<thread>... <k>.</k> <holds>H</holds> <id>T</id> ...</thread> => .)
        <busy> Busy => Busy -Set keys(H) </busy>
        <terminated>... . => SetItem(T) ...</terminated>

   rule <k> join T:Int; => . ...</k>
        <terminated>... SetItem(T) ...</terminated>

//@ \subsubsection{Acquire lock}

   rule <k> acquire V:Val; => . ...</k>
        <holds>... . => V |-> 0 ...</holds>
        <busy> Busy (. => SetItem(V)) </busy>
        when (notBool(V in Busy:Set))
        [transition]

   rule <k> acquire V; => . ...</k>
        <holds>... V:Val |-> (N:Int => N +Int 1) ...</holds>

//@ \subsubsection{Release lock}

   rule <k> release V:Val; => . ...</k>
        <holds>... V|->(N => N:Int -Int 1) ...</holds>
        when N >Int 0

   rule <k> release V; => . ...</k> <holds>... V:Val|->0 => . ...</holds>
        <busy>... SetItem(V)=>. ...</busy>

//@ \subsubsection{Rendezvous synchronization}

   rule <k> rendezvous V:Val; => . ...</k>
        <k> rendezvous V; => . ...</k>  [transition]

//@ \section{Auxiliary declarations and operations}

  syntax Exp ::= lvalue(K)
  syntax Val ::= loc(Int)

  rule <k> lvalue(X:Id) => loc(L) ...</k>  <env>... X |-> L:Int ...</env>
    [structural]

  context lvalue(_[HOLE])
  context lvalue(HOLE[_])

  rule lvalue(lookup(L:Int)) => loc(L)  [structural]

//@ \subsection{Sequences of locations}

  syntax Map ::= Int "..." Int "|->" K
    [function, latex({#1}\ldots{#2}\mapsto{#3})]
  rule N...M |-> _ => .Map  when N >Int M
  rule N...M |-> K => N |-> K (N +Int 1)...M |-> K  when N <=Int M

  syntax Type ::= type(K)  [function]
  rule type(_:Int) => int
  rule type(_:Bool) => bool
  rule type(_:String) => string
  rule type(array(T,_,_)) => (T[])   // () needed! K parses [] as no rule tags
  rule type(lambda(T,Ps,_)) => types(Ps) -> T
  rule type(undefined(T)) => T
  rule type(nothing(T)) => T

  syntax Types ::= types(Params)  [function]
  rule types(T:Type _:Id) => T, .Types
  rule types(T:Type _:Id, P, Ps) => T, types(P,Ps)
  rule types(.Params) => void, .Types
endmodule
