module CINK-BASIC-SYNTAX 

  /*@ \subsection{Declarations}
    The declarations are used for declaring variables and function names
    together with their return types.
    We consider only integer and boolean variables. A return type of a function
    could be an integer, a boolean, or \texttt{void}.
  */

  syntax PrimType ::= "int" | "bool" | "void" 

  syntax Type ::= PrimType

  syntax Decl ::= Type Exps


  /*@ \subsection{Expressions} */

  /*@ The constants of the builtin types are primitive constructs and therefore
      they should be values.  
      The sort for values will be extended in the module describing the 
      semantics. 
      We prefer to declare \texttt{cin} and \texttt{cout} as values rather 
      than identifiers; the reason for this decision will be explained later.
   */

  syntax Val ::= "cout" | "cin" | Bool | String | Int

  /*@
    We included in CinK a small subset of \Cpp language, the missing operators
    can be easily added in a similar way. Recall that the most important (from
    the semantic point of view) thing we have to mention for operators is the
    attribute \texttt{strict}, that specifies the evaluation order of the 
    operands. For instance, the arithmetic binary 
    operators are strict in both arguments, hence the behavior of some 
    programs could be undefined or non-determinsitic because the evaluation
    of the arguments could have side-effects.  The assignment operator is strict
    only in the second argument because the first argument must be evaluated 
    to an l-value. These features are common to many languages. In contrast
    to the other examples, the function call expression is strict only in the
    first argument (the function name) because the evaluation of the arguments
    it is depending on the bindding mechanism of the corresponding argument: 
    this can be call-by-value or call-by-reference. These two mechansims will
    be explained later. 
   */
  syntax Exp ::= Id | Val
               | "(" Exp ")"  [bracket]
               | Exp "(" Exps ")" [strict(1)]
               > left:
                 Exp "*" Exp [strict, multiply]
               | Exp "/" Exp [strict, divide]
               | Exp "%" Exp [strict, latex({#1}\%{#2}), modulo] 
               >  left:
                 Exp "+" Exp [strict, plus]
               | Exp "-" Exp [strict, minus]
               > left:
                 Exp "<" Exp  [strict, lessthan]
               | Exp ">" Exp  [strict, greatthan]
               | Exp "<=" Exp [strict, latex({#1}\leq{#2}), lessequal]
               | Exp "==" Exp [strict, equality]
               >
                 "!" Exp [strict, negation] 
               > 
                 Exp "&&" Exp [left, strict(1), latex({#1}\mathrel{\&\&}{#2}), conjunction]
               > 
                 Exp "||" Exp [left, strict(1), disjunction]
               > left:
                 Exp "<<" Exp [left, seqstrict, latex({#1}\mathrel{\tt <<}{#2}), write]
               | Exp ">>" Exp [left, latex({#1}\mathrel{\tt >>}{#2}), read]
               >
                 Exp "=" Exp [right, strict(2), assign]
               >
                 "endl"

  /*@ \subsection{Statements}
    For now, we include in CinK only (a subset) of the imperative statements:
    expresion statement, bloc, sequential composition, while, and conditionals.
    We also added a minimal support for threads, similar to IMPPP, but using a
    \Cpp syntax and semantics.
   */

  syntax Stmt ::= Exp ";" [strict]
               | "#include" "<iostream>" 
               | "using" "namespace" "std" ";" 
                 [latex(\texttt{using namespace std;})]
               | Decl ";" [klabel(declStmt)]
               | "{" "}"
               | "{" Stmts "}"
               | "while" "(" Exp ")" Stmt 
               | "return" Exps ";" [strict]
               | Decl "(" Decls ")" "{" Stmts "}"
               | "if" "(" Exp ")" Stmt "else" Stmt [strict(1)]
               >
                 "if" "(" Exp ")" Stmt
  /*@
    A program is a sequence of statements:
  */
  syntax Pgm ::= Stmts 
  syntax Stmts ::= Stmt | Stmts Stmts [left]

  /* \subsection{Lists} */

  /*@
    The above definitions are using lists of expressions and lists of 
    declarations, which are declared as follows:
  */
  syntax Exps  ::= List{Exp,  ","} [strict]
  syntax Decls ::= List{Decl, ","} [strict]
//  syntax Stmts ::= List{Stmt,""}

endmodule

module CINK-BASIC-SEMANTICS
  imports CINK-BASIC-SYNTAX

  /*@ \subsection{Values.} 
    The values are a very important syntactic category in the definition
    of any language; with them, we are able to know when the evaluation
    of an expression is finished. This piece of information is crucial, e.g.,
    for the heating and cooling rules. 
    We already defined the subset of values that is part of the syntax, 
    namely the values given by the primitive types. Here we estend the set
    o values with intermediate constructs needed to execute programs. 
    Such a value is\texttt{noVal}, which "paradoxally" denotes in fact 
    "no value". The lambda abstractions are used for storing the
    functions. Similar to other \K examples (IMP, IMPPP, SIMPLE), the 
    functions are stored similar to variables and therefore their definitions
    are seen as values.
    As usual, all values must be subsorted to the \texttt{KResult} sort.
   */


  syntax Val ::= "noVal" 
               | "lambda" "(" Decls "@" Stmts ")" 
                 [latex(\lambda\,{#1}\mathrel{\bullet}{#2})]

  syntax Vals ::= List{Val,","}
  syntax KResult ::= Val
  syntax Exp ::= "undefined"

  /*@ \subsection{Memory Locations} */

  syntax Loc ::= "noLoc"


  /*@ \subsection{Auxiliary constructs.} */


  /*@
    \texttt{execute} is used to start the computation of a program; and
    \texttt{noname} for the initial name of a thread.
  */
  syntax K ::= "execute"

 /*@
   The next two constructors are used for storing the enavironment and the
   rest of the computation in the call stack (\texttt{fstack}). 
 */

  syntax ListItem ::= "(" List "," K ")"
                    | "[" Map "]"

 /*@ \subsection{Configuration.} 
   The configuration is standard for such languages (compare it to that of IMPP
   and SIMPLE).
   The threads are included in a cell named \texttt{threads}, where each cell
   \texttt{thread}, representing the current of a thread, includes a cell 
   \texttt{k} for the local computations, a cell \texttt{env} for the local
   environment, and a cell \texttt{fstack} for
   the managing the local configurations when a function call expression 
   or a return statement is executed.
  */

  configuration       <k color="green"> ($PGM:Pgm ~> execute) </k>
                      <env color="LightSkyBlue"> .Map </env>
                      <fstack color="orange"> .List </fstack>
                  <genv color="SkyBlue"> .Map </genv>
                  <store color="white"> .Map </store>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="Orchid" stream="stdout"> .List </out>



  /*@
    In order to have a minimal set of rules, some syntactic constructs
    are desugared. The desugaring can be done using the structural rules.
   */

  /*@ The desugaring rule for the if-then statement: */
  rule if(B:Exp) St:Stmt => if(B) St else {}  [macro]
  
  /*@
    The desugaring rule for statements declaring multiple variables.
   */

  rule T:Type E:Exp, E':Exp, Es:Exps ; => T E; T E'; T Es; [macro]

 /*@
    Desugaring rule for variable declarations with initialization.
  */

   rule T:Type E1:Exp = E2:Exp ; => T E1; E1 = E2;
        when isAliasExp(E1) =/=K true
        [macro]


  /*@ \subsection{Declarations.} */

  /*@
    Function declaration: a function is a stored similar to a variable,
    where the value stored in the associated location is the lambda
    abstraction of the function. 
   */


  rule <k>  (Decl:Decl (Xl:Decls) {Sts:Stmts})::Stmt  => .  ...</k> 
       <env>... . =>  (getName(Decl) |-> L) ...</env>
       <store>... . => (L |-> lambda(Xl @ Sts)) ...</store>
       when fresh(L:Loc)
       [fun-decl, structural]

  /*@
    The rules for variable declarations:
   */

  rule [var-decl] :
       <k> T:PrimType X:Id; => .  ...</k>      
       <env> Env:Map => Env[L/X] </env>
       <store>... . => (L |-> undefined) ...</store>
  when fresh(L:Loc)
       [structural]

  rule T:Type .Exps; => . [structural]


  /*@ The following two constructs have no semantics yet;
      they are used now only  for having a full compatibility with \Cpp,
      e.g., the \Cink programs can be 
      compiled with a \Cpp compiler. */
  rule #include <iostream> => . 
       [include, structural]

  rule using namespace std;=> .
       [using, structural]

  /*@ 
    The auxiliary construct \texttt{execute} is used to initialize the 
    execution of a program, which for the case of \Cink consists of the call
    of the main function.
  */

  rule <k> execute => String2Id("main")(.Vals); </k>
       <env> Env:Map </env>
       <genv> . => Env:Map </genv>
       [main, structural]
  
  /*@ \subsection{Expressions Evaluation.} */

  /*@
   The following expressions are strict. 
  */
  rule I1:Int + I2:Int => I1 +Int I2 [plus,structural]

  rule I1:Int - I2:Int => I1 -Int I2 [structural]

  rule I1:Int * I2:Int => I1 *Int I2 [structural]

  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=Int 0 [structural]
 
  rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=Int 0 [structural]

  rule I1:Int < I2:Int => (I1 <Int I2) [structural]

  rule I1:Int > I2:Int => (I1 >Int I2) [structural]

  rule I1:Int <= I2:Int => (I1 <=Int I2) [structural]

  rule I1:Int == I2:Int => (I1 ==Int I2) [structural]
 
  /*@
   Here are the rules for the expressions having the strict attribute 
   declared in the syntax.
  */

  rule true && B:Exp => B [structural]
  rule false && B:Exp => false [structural]
  rule true || B:Exp => true [structural]
  rule false || B:Exp => B [structural]
  rule ! false  => true [structural]
  rule ! true => false [structural]

  rule endl => "\n" [structural]


  /*@ \subsection{Memmory operations.} */


  /*@
    The evaluation of a variable name as an r-value:
  */
  rule <k> X:Id => V ...</k>
       <env>... X |-> L:Loc ...</env>
       <store>... L |-> V:Val ...</store>
       [kripke(mem-lookup)]

  /*@
    The memory update is given by the assignment operator. We consider
    here only the case when he left-hand side is an variable name. 
    The general case will be considered in a future iteration.
   */
  rule <k> X:Id = V:Val => V  ...</k>
       <env>... X |-> L:Loc ...</env>
       <store>... L |-> (_ => V) ...</store>
       [kripke(mem-update)]

  /* \subsection{Control Statements.} */

  /*@
    As usual, the \texttt{while} statement is desugared using the 
    \texttt{if-then-else} statement.
  */
  rule while(B:Exp) St:Stmt => if (B) {St while(B) St} else {}
       [while, structural]

  /*@
    Since \texttt{if} is strict in the first argument, which is a boolean
    expression, proceed by case-analysis on the result values:
  */
  rule if(false) _ else St:Stmt => St [if-false]
  rule if(true) St:Stmt else _ => St [if-true]


  /*@
    The semantics of the expression statement consists of removing the
    value obtained by evaluating the expression. Recall that the statement
    is strict.
   */
  rule <k> (V:Val; ~> K:K) => K </k> 
       when K =/=K .K
       [instr-expr]
  /*@
    Block. Note that in this iteration we assume that the blocks do not include
    variable declarations. This will be added in a future iteration.\\
      -- the case of non-empty block
  */
  rule { Sts:Stmts } => Sts
       [block, structural]

  /*@ -- the case of the empty block: */
  rule {} => .  [block-empty, structural]

  //@ The sequential composition is just a sequence of computations:
  rule (Sts:Stmts Sts':Stmts) => (Sts ~> Sts')
       [seq-comp, structural] 

//  rule .Stmts => .K

  /*@ \subsection{Input/Output Statements.} */

  /*@ Writting in the the standard stream \texttt{cout}: */
  rule <k> cout << V:Val => cout  ...</k>  
       <out>... . => (ListItem(V) ListItem(" ")) </out>
       [print-stream, print]

  /*@
   In order to read from the standard stream \texttt{cin}, the expression
   from the right-hand side must be evaluated to an l-value:
  */
  rule <k> cin >> X:Id => cin  ...</k>
       <env>...  X |-> L:Loc  ...</env>
       <store>... L |-> (_ => I)  ...</store>
       <in> (ListItem(I:Int) => .)  ...</in>
       [read-stream]

  /*@
    \subsection{The function call expression}
    The function name is evaluated to its value, which is a lambda 
    abstraction: $\it Xl$ is the list of parameters, $\it Sts$ is body of
    the function. The {\sc function-call} rule pushes the calling context,
    i.e., the remainder of the computation $K$ and environment stack 
    (including the current environment) on top of the function stack, 
    while the {\sc return} rule uses the information there to restore 
    the environment and computation of the caller.
    Since the evaluation strategy for the second argument is depending on
    the binding specification in the function signature, the function call
    expression is declared strict only in its first argument.
    Note that in this iterartion we consider only the call-by-value 
    binding mechanism. The call-by-reference mechanism will be considered
    in a future iteration.
   */

  /*@
    The rule defining the evaluation of a function call expression evaluates
    first the actual parameters, and then binds the 
    values to the formal parameters and executes the body, while saving the
    calling context in case of an abrupt return. This is done by mimic the
    heating-cooling mechanism (the first rule is a heating-like one, and the
    second a cooling-like one).
   */

  rule <k> lambda(Xl:Decls @ Sts:Stmts)(El:Exps)
           =>
           evaluate El to .Vals following Xl; ~>
           lambda(Xl:Decls @ Sts:Stmts)(HOLE)
       ...</k> 

  rule <k> (Vl:Vals ~> lambda(Xl:Decls @ Sts:Stmts)(HOLE) ~> K:K)
           => 
           (bind Vl to Xl; ~> Sts ~> return noVal;)
       </k>
       <br/>
       <genv> GEnv:Map </genv>
       <env> Env:Map => GEnv </env>
       <fstack> . => ([Env], K) ...</fstack>
       [fun-call]

  /*@
    To evaluate actual parameters according to their declared strategy we will
    make use of the power of \K evaluation contexts. 
    The actual parameters must be evaluated using 
    the $\terminalNoSpace{evaluate}$ construct and $\terminalNoSpace{following}$ 
    the list of formal parameters.
  */

  syntax Exps ::= "evaluate" Exps "to" Vals "following" Decls ";"

  /*@
    For a formal parameter declared with the call-by-value mechanism,
    the corresponding argument expression must be evaluated to an rvalue as
    specified by by the following contextual declaration:
  */

  context evaluate (HOLE, _:Exps) to _:Vals following (T X:Id, _:Decls);


  /*@
    \noindent This second context uses again the special type of context used
    above for $\terminalNoSpace{evaluate}$, by requesting that the expression
    on position $\khole{}$ be evaluated as an lvalue.
    \par
    The following two rules, together with the strict evaluation strategy for
    lists of expressions complete the semantics of $\terminalNoSpace{evaluate}$
    by recursing into the lists:
  */

  rule evaluate(V:Val, El:Exps => El) to (Vl:Vals => append(Vl, V))
         following (Dec:Decl, Xl:Decls => Xl);
       [structural]
   
  rule evaluate .Exps to Vl:Vals following .Decls; => Vl [structural]

   /*@
     \subsubsection{Binding mechanisms}
     Similarly to the evaluation rules, the binding rules are also different 
     for the two parameter passing styles.
     As we have already seen, the binding is performed using an auxiliary 
     construction:
   */

  syntax K ::= "bind" Vals "to" Decls ";"  

  /*@
  For call-by-value, the passed value $V$ is stored into a new memory location
  which is bound to the formal parameter:
  */
  rule <k> bind((V:Val, Vs:Vals) => Vs)
           to((T X:Id, Xl:Decls) => Xl); 
       ...</k>
       <env> Env:Map => Env[L/X] </env>
       <store>... . => L |-> V ...</store>
when fresh(L:Loc)
       [structural]

  /*@
    Finally, once all parameters have been bound, the binding construct 
    dissolves:
   */
  rule bind .Vals to .Decls; => . [ structural ]

  /*@
    \subsection{Function Return.}
    Similar to \Cpp, the argument of a return statement is a list of
    expressions (note that Cink does not have yet a distinguished
    definition for the comma operator). 
  */

  /*@
    Similar to the comma operator, the evaluation of the return argument
    is given from left to right. Since the expression lists are strict,
    we get this feature for free provided the declaration for return is
    strict. Remains oly to write rules keeping the last value from the list.
  */

  rule return _:Val, V:Val, Vs:Vals ; => return V, Vs ; 
       [return]

  rule <k> (return V:Val; ~> _) => (V ~> K) </k>
       <env> _ => Env </env>
       <fstack> ([Env:Map], K:K) => . ...</fstack>
       [return]

  /*@
    \subsection{Auxiliary Functions and Rules.}
    Here we winclude the semantics for the auxiliary constructs, used to give
    semnatics for \Cink.
  */

  syntax Bool ::= "isAliasExp" "(" Exp ")" [function]

  /*@
    The next operator returns the variable name from an expression occurring
    in a declaration:
  */
  syntax  Id ::= "getName" "(" K ")" [function]

  rule getName(X:Id) => X
  rule getName(T:Type E:Exp) => getName(E)
  rule getName(E1:Exp = E2:Exp) => getName(E1)

  //@ Append function:

  syntax Vals ::= "append" "(" Vals "," Val ")" [function]
  rule append(.Vals, V:Val) => V, .Vals
  rule append((V':Val, Vl:Vals), V:Val) => V', append(Vl, V)
  
endmodule
