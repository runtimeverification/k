module SIMPLE-UNTYPED-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS

/*@ \section{Syntax}
We start by defining the SIMPLE syntax.  The language constructs discussed
above have the expected syntax and evaluation strategies.  Recall that in \K
we annotate the syntax with appropriate strictness attributes, thus giving
each language construct the desired evaluation strategy. */

/*@ \subsection{Identifiers}
The special identifier for the function ``main'' belongs to all programs.
Each program may use additional identifiers, which need to be declared either
automatically (when one uses an external parser) or manually
(when one writes the program). */

/*@ \subsection{Declarations}
There are two types of declarations: for variables (including arrays) and
for functions. */

  syntax Start ::= Stmts
  syntax Ids ::= List{Id,","} [strict, cons("Ids1ListSyn"), hybrid]
  syntax Exps ::=  List{Exp,","} [cons("Exps1ListSyn")]


  syntax Decl ::= "var" Exps ";" [cons("Ddecl1VarDeclSyn")]
                | "function" Id "(" Ids ")" Stmt [cons("Ddecl1FuncDeclSyn")]

/*@ \subsection{Expressions}
The expression constructs below are standard.  Increment (\texttt{++}) takes
an expression rather than a variable because it can also increment an array
element.  Arrays can be multidimensional and can hold other arrays, so their
lookup operation takes a list of expressions as argument and applies to an
expression (which can in particular be another array lookup), respectively.
The construct \texttt{sizeof} gives the size of an array in number of elements
of its first dimension.  Note that almost all constructs are strict.
Exceptions are the increment (since its first argument gets updated, so it
cannot be evaluated) and the assignment which is only strict in its second
argument (for the same reason as the increment). */

  syntax Exp ::= Int | Bool | Id | String
               | "(" Exp ")"            [bracket]
               | "++" Exp        
               > Exp "[" Exps "]"        [strict]
               > Exp "(" Exps ")"        [strict]
               | "-" Exp                 [strict]
               | "sizeOf" "(" Exp ")"    [strict]
               | "read" "(" ")"    
               > left:
                    Exp "*" Exp          [strict, left]
               | Exp "/" Exp             [strict, left
               | Exp "%" Exp             [strict, left]
               > left:
                    Exp "+" Exp          [strict, left]
               | Exp "-" Exp             [strict, left]
               > non-assoc:
                    Exp "<" Exp          [strict, non-assoc]
               | Exp "<=" Exp            [strict, non-assoc]
               | Exp ">" Exp             [strict, non-assoc]
               | Exp ">=" Exp            [strict, non-assoc]
               | Exp "==" Exp            [strict, non-assoc]
               | Exp "!=" Exp            [strict, non-assoc]
               > "not" Exp               [strict]
               > left:
                    Exp "and" Exp        [strict, left]
               | Exp "or" Exp            [strict, left]
               > Exp "=" Exp             [strict(2), right]

/*@ \subsection{Statements}
Most of the statement constructs are standard for imperative languages.
We syntactically distinguish between empty and non-empty blocks, because we
chose \textit{Stmts} not to be a (``\texttt{;}''-separated) list of
\textit{Stmt}.  Variables can be declared anywhere inside a block, their scope
ending with the block.  Expressions are allowed to be used for their side
effects only (followed by a semicolon ``\texttt{;}'').  Functions are allowed
to abruptly return.  The exceptions are parametric, i.e., one can throw a value
which is bound to the variable declared by \texttt{catch}.  Threads can be
dynamically created and terminated, and can synchronize with \texttt{acquire},
\texttt{release} and \texttt{rendezvous}.  Note that the strictness attributes
obey the intended evaluation strategy of the various constructs.  In
particular, the if-then-else construct is strict only in its first argument
(the if-then construct will be desugared into if-then-else), while the loops
constructs are not strict in any arguments.  The \texttt{print} statement
constructs is variadic, that is, it takes an arbitrary number of arguments. */

  syntax Stmt ::= "{" "}"        
                | "{" Stmts "}"        
                | Exp ";"                             [strict]
                | "if" Exp "then" Stmt "else" Stmt    [avoid, strict(1)
                | "if" Exp "then" Stmt               
                | "while" Exp "do" Stmt               
                | "for" Id "=" Exp "to" Exp "do" Stmt  
                | "return" Exp ";"                    [strict]
                | "return" ";"                      
                | "write" "(" Exp ")" ";"             [strict]
                | "try" Stmt "catch" "(" Id ")" Stmt 
                | "throw" Exp ";"                     [strict]
                | "spawn" Stmt                     
                | "acquire" Exp ";"                   [strict]
                | "release" Exp ";"                   [strict]
                | "rendezvous" Exp ";"                [strict]
                | "print" "(" Exps ")" ";"            [strict]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts                        [right]

/*@ \section{Desugared Syntax}
This part desugars some of SIMPLE's language constructs into core ones.
We only want to give semantics to core constructs, so we get rid of the
derived ones before we start the semantics.  All desugaring macros below are
straightforward.  For the semantics, we can therefore assume that all
functions take a list of arguments, that each conditional has both branches,
that there are only \texttt{while} loops, and that each variable is
declared alone and is initialized. */

  rule if E:Exp then S:Stmt => if E then S else {}
  rule (for X:Id = E1 to E2 do S) => {var X=E1; while X <= E2 do {S X = (X + 1);}}
  rule var E1:Exp, E2:Exp, Es:Exps; => var E1; var E2, Es;
  rule var X:Id = E:Exp; => var X; X = E;

  syntax #Id ::= "main"

endmodule






module SIMPLE-UNTYPED
  imports SIMPLE-UNTYPED-SYNTAX
  imports BUILTIN-HOOKS

  syntax Val ::= Int | Bool | String
               | "arrayRef" "(" Int "," Int ")" [cons("Val1ArrayRefSyn")]
               | "lambda" "(" Ids "," Stmt ")"  [cons("Val1LambdaSyn")]
  syntax Vals ::= List{Val,","} [cons("Vals1ListSyn")]
  syntax Exp ::= Val
  syntax KResult ::= Val

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> ($PGM:K ~> execute) </k>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
                      </control>
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Map </holds>
                    </thread>
                  </threads>
                  //<br/>
                  <genv color="pink"> .Map </genv>
                  <store color="white"> .Map </store>
                  <busy color="cyan">.Set</busy>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="brown" stream="stdout"> .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
                </T>


  syntax K ::= "undefined"  [cons("K1UndefinedSyn")]


  rule <k> var X:Id; => . ...</k>
       <env> Env:Map => Env[L:Int/X] </env>
       <store>... . => L|->undefined ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>

  rule <k> var X[N:Int]; => . ...</k>
       <env> Env => Env:Map[L/X:Id] </env>
       <store>... . => L |-> arrayRef(L +Int 1, N)
                       (L +Int 1) .. (L +Int N) |-> undefined ...</store>
       <nextLoc> L => (L:Int +Int 1) +Int N </nextLoc>


  context var X:Id[HOLE],.Exps;

  syntax #Id ::= "$1" | "$2"
  rule var X:Id[N1:Int,N2:Int,Vs:Vals]; =>
       var X[N1];
       {
         var $1 = X;
         for $2 = 0 to N1 - 1 do   // no longer a stupid parser
         {
           var X[N2,Vs];    // no longer a stupid parser
           $1[$2] = X;
         }
       }  [structural]

  rule <k> function F:Id(Xs:Ids) S => . ...</k>
       <env> Env => Env[L/F] </env>
       <store>... . => L|->lambda(Xs,S) ...</store>
       <nextLoc> L => L:Int +Int 1 </nextLoc>



  syntax K ::= "execute" [cons("K1ExecuteSyn")]
  rule <k> execute => (main(.Exps);) </k>
       <env> Env </env> <genv> . => Env </genv>  [structural]



  rule [look-up]:
       <k> X:Id => V:Val ...</k>
       <env>...X|->L...</env>
       <store>...L|->V...</store>  [transition]



  context ++(HOLE => lvalue(HOLE))
  rule <k> ++loc(L) => I:Int +Int 1 ...</k>
       <store>... L:Int |-> (I => I +Int 1) ...</store>  [transition]

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
  rule B1:Bool and B2:Bool => B1 andBool B2
  rule B1:Bool or B2:Bool => B1 orBool B2
  rule not(B:Bool) => notBool(B)


  rule V:Val[N1:Int,N2:Int,Vs:Vals] 
    => V[N1,.Exps][N2,Vs]  [structural, anywhere]
  rule arrayRef(L,_:Int)[N] => lookup(L:Int +Int N:Int)  
    [structural, anywhere]
  syntax K ::= "lookup" "(" Int ")" [cons("K1LookupSyn")]
  rule <k> lookup(L:Int) => V:Val ...</k> <store>...L|->V...</store>  [transition]

  rule sizeOf(arrayRef(_:Int,N:Int)) => N

  syntax ListItem ::=  "(" Map "," K "," Bag ")" [cons("ListItem1MKBSyn")]

  rule <k> lambda(Xs:Ids,S)(Vs:Vals) ~> K:K
        => bindto(Xs,Vs) ~> S ~> return; </k>
       <control> <fstack> . => (Env,K,C) ...</fstack> C:Bag </control>
       <env> Env => GEnv </env>
       <genv> GEnv:Map </genv>
  rule <k> return(V); ~> _ => V ~> K </k>
       <control> <fstack> (Env,K,C) => . ...</fstack> (_ => C) </control>
       <env> _ => Env </env>
  syntax Val ::= "nothing" [cons("Val1NothingSyn")]
  rule return; => return nothing;   [structural]


  syntax K ::= "bindto" "(" Ids "," Vals ")" [cons("K1BindToSyn")]
  rule <k> bindto((X:Id,Xs => Xs),(V,Vs:Vals => Vs)) ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> V:Val ...</store>
       <nextLoc> L => L:Int +Int 1 </nextLoc>
  rule <k> bindto(.Ids,.Vals) => . ...</k>  [structural]

  rule <k> read() => I ...</k> <in> ListItem(I:Int) => . ...</in>  [transition]


  context (HOLE => lvalue(HOLE)) = _
  rule <k> loc(L:Int)=V:Val => V ...</k>
       <store>... L|->(_=>V) ...</store> [transition]

  rule {} => . [structural]
  rule <k> {Ss:Stmts} => Ss~>env(Env) ...</k> <env> Env </env>  [structural]


  syntax K ::= "env" "(" Map ")" [cons("K1EnvSyn")]
  rule <k> env(Env) => . ...</k> <env> _ => Env </env>  [structural]


  rule (env(_) => .) ~> env(_)  [structural]


  rule S1 S2 => S1 ~> S2  [structural]

  rule V:Val; => .

  rule if  true then S else _ => S
  rule if false then _ else S => S

  rule <k> while E:Exp do S
    => if E then {S while E do S} else {} ...</k>  [structural]

  rule <k> print(V,Vs => Vs); ...</k>
       <out>... . => ListItem(V) </out>  [transition]
  rule print(.Vals); => .                [structural]


  syntax ListItem ::= "(" Id "," Stmt "," K "," Map "," Bag ")" [cons("ListItem1ISKMBSyn")]
  syntax K ::= "popx" [cons("K1PopxSyn")]
  rule <k> (try S1 catch(X) S2 => S1 ~> popx) ~> K </k>
       <control> <xstack> . => (X:Id,S2,K,Env,C) ...</xstack> C:Bag </control>
       <env> Env </env>
  rule <k> popx => . ...</k> <xstack> _:ListItem => . ...</xstack>
  rule <k> throw V; ~> _ => {var X:Id=V; S2} ~> K </k>
       <control> <xstack> (X:Id,S2,K,Env,C) => . ...</xstack> (_ => C) </control>
       <env> _ => Env </env>


   rule <thread>... <k> spawn S => . ...</k> <env> Env </env> ...</thread>
        (. => <thread>... <k> S </k> <env> Env </env> ...</thread>)

   rule (<thread>... <k>.K</k> <holds> H:Map </holds> ...</thread> => .)
        <busy> Busy:Set => Busy -Set keys(H) </busy>


   rule <k> acquire V; => . ...</k> <holds>... . => V|->0 ...</holds>
        <busy> Busy (. => SetItem(V)) </busy>
     when (notBool(V in Busy:Set)) [transition]
   rule <k> acquire V; => . ...</k> <holds>... V:Val|->(N => N:Int +Int 1) ...</holds>


   rule <k> release V:Val; => . ...</k>
        <holds>... V|->(N => N:Int -Int 1) ...</holds>
     when N >Int 0
   // used prefix notation for -Int because of parsing problems
   rule <k> release V; => . ...</k> <holds>... V:Val|->0 => . ...</holds>
        <busy>... SetItem(V)=>. ...</busy>


   rule <k> rendezvous V:Val; => . ...</k>
        <k> rendezvous V; => . ...</k>  [transition]

// For parsing reasons, we prefer to allow lvalue to take a K
  syntax Exp ::= "lvalue" "(" K ")" [cons("Exp1LValueSyn")]
  syntax Val ::= "loc" "(" Int ")" [cons("Val1LocSyn")]
// Local variable
  rule <k> lvalue(X:Id) => loc(L:Int) ...</k>
       <env>... X|->L ...</env>  [structural]
// Array element: evaluate the array and its index;
// then the array lookup rule above applies.
  context lvalue(_[HOLE])
  context lvalue(HOLE[_])
// Finally, return the address of the desired object member
  rule <k> lvalue(lookup(L:Int)) => loc(L) ...</k>  [structural]



  syntax List{K} ::= Int ".." Int [cons("ListDlKDr1DotDotSyn")]
  rule N1:Int..N2:Int => .List{K}              when N1  >Int N2  [structural, function, anywhere]
  rule N1:Int..N2:Int => N1 ,, (N1 +Int 1)..N2 when N1 <=Int N2  [structural, function, anywhere]

endmodule 
