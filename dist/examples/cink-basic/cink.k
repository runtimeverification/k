module CINK-SYNTAX 

  imports BUILTIN-SYNTAX-HOOKS

  /* \subsection{Declarations} */

  syntax Decl ::= "int"  Exp 
                | "void" Id 
                | "bool" Exp

  /* \subsection{Expressions} */

  syntax Exp ::= Id | Int | Bool | String | Val
               | "(" Exp ")"  [bracket]
               | Id "(" Exps ")" [prec(0), strict(1)]
               | "&" Exp
               > left:
                 Exp "*" Exp [left, strict]
               | Exp "/" Exp [left, strict]
               | Exp "%" Exp [left, strict] 
               >  left:
                 Exp "+" Exp [left, strict]
               | Exp "-" Exp [left, strict]
               > left:
                 Exp ">" Exp [left, strict]
               | Exp "<=" Exp [left, strict, latex("{#1}\leq{#2}")] 
               | Exp "==" Exp [left, strict]
               >
                 "!" Exp [strict] 
               > 
                 Exp "&&" Exp [left, strict(1)]
               > 
                Exp "||" Exp [left, strict(1)]
               > left:
                 Exp "<<" Exp [left, strict]
               | Exp ">>" Exp [left, strict(1)]
               >
                 Exp "=" Exp [right, strict(2)]
               

  syntax #Id ::= "main" 
  syntax Val ::= "cout" | "cin"

  /* \subsection{Statements} */

  syntax Stmt ::= Exp ";" [strict]
               | Decl ";"
               | "{" "}"
               | "{" Stmts "}"
               | "while" "(" Exp ")" Stmt 
               | "return" Exps ";" // [strict]
               | Decl "(" Decls ")" "{" Stmts "}"
               | "#include" "<iostream>"
               | "if" "(" Exp ")" Stmt "else" Stmt [strict(1)]
               >
                 "if" "(" Exp ")" Stmt

  syntax Pgm ::= Stmts 

  /* \subsection{Lists} */

//  syntax Stmts ::= List{Stmt,""}
  syntax Stmts ::= Stmt | Stmts Stmts [left]

  syntax Exps  ::= List{Exp,  ","} [strict]
  syntax Decls ::= List{Decl, ","}


endmodule

module CINK 
  imports CINK-SYNTAX

  /* \subsection{ASTs which are results.} */

  syntax Val ::= Int | Bool | String | "void" 
               | "lambda" "(" Decls "@" Stmts ")" [latex("")]
               | "loc" "(" Int ")"

  syntax Vals ::= List{Val,","}
  syntax KResult ::= Val

  /* \subsection{Auxiliary constructs.} */

  // extends the expressions with other constructs
  syntax Exp ::=  "lvalue" "(" K ")"
               | "valFromLoc" "(" K ")" [strict]

  syntax K ::= "undefined" | "execute"

  syntax ListItem ::= "(" List "," K ")"
                    | "[" Map "]"

 /* \subsection{Configuration.} */
  configuration <T color="yellow">
                  <k color="green"> ($PGM:Pgm ~> execute) </k>
                  <env color="LightSkyBlue"> .Map </env>
                  <genv color="SkyBlue"> .Map </genv>
                  <store color="white"> .Map </store>
//                  <br/>
                  <fstack color="orange"> .List </fstack>
                  <bstack color="orange"> .List </bstack>
                  <in color="magenta" stream="stdin"> $IN:List </in>
//                  <out color="Orchid"> .List </out>
                  <out color="Orchid" stream="stdout"> .List </out>
                  <nextLoc> 0 </nextLoc>
                </T>

// macros
  rule if(B:Exp) St:Stmt => if(B) St else {}  [anywhere]
  rule '_`(_`)(X:Id,,E:Exp) => '_`(_`)(X,,'_`,_(E,, .Exps))  [anywhere]
  rule void X:Id => int X  [anywhere]
  rule '_;('int_('_=_(X:Id,, A:Exp)))
       =>
       '__('_;(int X),, '_;('_=_(X,, A)))
       [anywhere]
  rule '_;('bool_('_=_(X:Id,, B:Exp)))
       =>
       '__('_;(int X),, '_;('_=_(X,, B)))
       [anywhere]

  
  /* \subsection{Expressions Evaluation.} */
  rule I1:Int + I2:Int => I1 +Int I2 [structural]
  rule I1:Int - I2:Int => I1 -Int I2 [structural]
  rule I1:Int * I2:Int => I1 *Int I2 [structural]
  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=Int 0 [structural]
  rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=Int 0 [structural]

  rule I1:Int > I2:Int => (I1 >Int I2) [structural]
  rule I1:Int <= I2:Int => (I1 <=Int I2) [structural]
  rule I1:Int == I2:Int => (I1 ==Int I2) [structural]
 
  rule true && B:Exp => B [structural]
  rule false && B:Exp => false [structural]
  rule true || B:Exp => true [structural]
  rule false || B:Exp => B [structural]
  rule ! false  => true [structural]
  rule ! true => false [structural]


  syntax  Id ::= "getName" "(" Decl ")" [function]

  rule getName(int  X:Id) => X     [anywhere]
  rule getName(bool X:Id) => X     [anywhere]
  rule getName(int  & X:Id) => X   [anywhere]
  rule getName(bool & X:Id) => X   [anywhere]
  rule getName('void_(X:Id)) => X  [anywhere]


  /* \subsection{Declarations.} */
  rule [fun-decl] :
       <k> '_`(_`)`{_`}(Decl:Decl,, Xl:Decls,, Sts:Stmts) => .  ...</k> 
       <env>... . =>  (getName(Decl) |-> L) ...</env>
       <store>... . => (L |-> lambda(Xl @ Sts)) ...</store>
       <nextLoc> L:Int => (L +Int 1) </nextLoc>
       [structural]

   rule [var-decl] :
       <k> Decl:Decl => void  ...</k>      
       <env> Env:Map => Env[L/getName(Decl)] </env>
       <store>... . => (L |-> undefined) ...</store>
       <nextLoc> L:Int => (L +Int 1) </nextLoc>
      [structural]

   rule [alias-decl] :
       <k> int & X:Id = Y:Id => void  ...</k>      
       <env> Y |-> L:Int (Env:Map => Env[L/X]) </env>
      [structural]

   rule [alias-decl] :
       <k> bool & X:Id = Y:Id => void  ...</k>      
       <env> Y |-> L:Int (Env:Map => Env[L/X]) </env>
      [structural]

  rule [include] :
       <k> #include <iostream> => .  ...</k>
       [structural]

  rule <k> execute => '_;('_`(_`)(main,, .Vals)) </k>
       <env> Env:Map </env>
       <genv> . => Env:Map </genv>
       [structural]

  /* \subsection{Memmory operations.} */


  rule [mem-lookup-lvalue] :
       <k> lvalue(X:Id) => loc(L) ...</k>
       <env>... X |-> L:Int ...</env>


  rule [mem-lookup-rvalue] :
       <k> X:Id => V ...</k>
       <env>... X |-> L:Int ...</env>
       <store>... L |-> V:Val ...</store>

  context (HOLE => lvalue(HOLE)) = _
  rule [mem-update] :
       <k> loc(L:Int) = V:Val => V  ...</k>
       <env>...  X |-> L  ...</env>
       <store>... L |-> (_ => V) ...</store>

  /* \subsection{Control Statements.} */
  rule [while] :
       while(B:Exp) St:Stmt => if (B) {St while(B) St} else {}
       [structural]

  rule [if-false] : if(false) _ else St:Stmt => St
  rule [if-true] : if(true) St:Stmt else _ => St

  rule [instr-expr] : 
       <k> (V:Val; ~> K:K) => K </k> 
       when K =/=K .K
//       [transition]

  rule [block] : 
       <k>{Sts:Stmts} => (Sts ~> popb)  ...</k>
       <env> Env:Map </env>
       <bstack> . => [Env] ...</bstack>
       [structural]

  rule [block-empty] : {} => .  [structural]

  rule [seq-comp] : (Sts:Stmts Sts':Stmts) => (Sts ~> Sts') [structural] 

  /* \subsection{Input/Output Statements.} */

  rule [print-stream]:
       <k> cout << V:Val => cout  ...</k>  
       <out>... . => (ListItem(V) ListItem(" ")) </out>

  rule [read-stream]:
       <k> cin >> X:Id => cin  ...</k>
       <env>...  X |-> L:Int  ...</env>
       <store>... L |-> (_ => I)  ...</store>
       <in> (ListItem(I:Int) => .)  ...</in>

  /* \subsection{Function Call.} */
  rule [fun-call] : 
       <k> ('_`(_`)(lambda(Xl:Decls @ Sts:Stmts),, El:Exps) ~> K:K)
           =>
           (bindto(Xl; El) ~> setEnv(GEnv) ~> Sts ~> return void;)
       </k> 
//       <br/>
       <genv> GEnv:Map </genv>
       <env> Env:Map </env>
       <bstack> Stack:List </bstack>
       <fstack> . => ([Env] Stack, K) ...</fstack>
//       [large]

  syntax K ::= "setEnv" "(" Map ")"

  rule <k> setEnv(Env:Map) => . ...</k>
       <env> _ => Env </env>

  /* \subsection{Function Return.} */

  rule [return] : return .Exps ; => return void; [structural]
  context return HOLE, Es:Exps ;
  rule [return] : return V:Val, Es:Exps ; => return Es ; 
       when Es =/=K .Exps 
       [structural]

  rule [return] :
       <k> (return V:Val; ~> _) => (V ~> K) </k>
       <env> _ => Env </env>
       <bstack> _ => Stack </bstack>
       <fstack> ([Env:Map] Stack:List, K:K) => . ...</fstack>
       [supercool]

  /* \subsection{Auxiliary Functions and Rules.} */


  // \texttt{bindto} binds formal parameters to actual parameters 

  syntax K ::= "bindto" "(" Decls ";" Exps ")"

  context bindto( (int X:Id, _:Decls); (HOLE, _:Exps) )

  rule <k> bindto(((int X:Id, Xl:Decls) => Xl); 
                  ((V:Val, Es:Exps) => Es))
           ~> setEnv(Env => Env[L/X]) 
       ...</k>
       <store>... . => L |-> V ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>

  context bindto( (int & X:Id, _:Decls); ((HOLE => lvalue(HOLE)), _:Exps) )

  rule <k> bindto(((int & X:Id, Xl:Decls) => Xl); 
                  ((loc(L:Int), Es:Exps) => Es))
           ~> setEnv(Env => Env[L/X]) 
       ...</k>

  rule <k> bindto(.Decls;.Vals) => . ...</k>  [ structural ]

  // \texttt{popb} pops out the stack of block environments
  syntax K ::= "popb"

  rule <k> popb => . ...</k>
       <bstack> [Env:Map] => . ...</bstack>
       <env> _ => Env </env> 


endmodule


