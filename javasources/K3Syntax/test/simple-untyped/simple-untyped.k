require "built-ins.k"

module SIMPLE-UNTYPED-SYNTAX
  including K
  syntax Start ::= Stmts
  syntax Ids ::= List{#Id,","} [strict, cons("Ids1ListSyn"), hybrid]
  syntax Exps ::=  List{Exp,","} [cons("Exps1ListSyn")]


  syntax Decl ::= "var" Exps ";" [cons("Ddecl1VarDeclSyn")]
                | "function" #Id "(" Ids ")" Stmt [cons("Ddecl1FuncDeclSyn")]

  syntax Exp ::= #Int | #Bool | #Id | #String
               | "(" Exp ")"            [bracket]
               | "++" Exp				[cons("Exp1PrefixPPSyn")]
               > Exp "[" Exps "]"	    [strict, cons("Exp1ArraySyn")]
               > Exp "(" Exps ")"	    [strict, cons("Exp1FuncCallSyn")]
               | "-" Exp             	[strict, cons("Exp1UMinusSyn")]
               | "sizeOf" "(" Exp ")"   [strict, cons("Exp1SizeSyn")]
               | "read" "(" ")"			[cons("Exp1Exp1ReadSyn")]
               > left:
               	 Exp "*" Exp         	[strict, left, cons("Exp1MulSyn")]
               | Exp "/" Exp         	[strict, left, cons("Exp1DivSyn")]
               | Exp "%" Exp         	[strict, left, cons("Exp1ModSyn")]
               > left:
               	 Exp "+" Exp         	[strict, left, cons("Exp1PlusSyn")]
               | Exp "-" Exp         	[strict, left, cons("Exp1MinusSyn")]
               > non-assoc:
               	 Exp "<" Exp         	[strict, non-assoc, cons("Exp1LTSyn")]
               | Exp "<=" Exp        	[strict, non-assoc, cons("Exp1LTESyn")]
               | Exp ">" Exp         	[strict, non-assoc, cons("Exp1GTSyn")]
               | Exp ">=" Exp        	[strict, non-assoc, cons("Exp1GTESyn")]
               | Exp "==" Exp        	[strict, non-assoc, cons("Exp1EQSyn")]
               | Exp "!=" Exp        	[strict, non-assoc, cons("Exp1NEQSyn")]
               > "not" Exp           	[strict, cons("Exp1NotSyn")]
               > left:
               	 Exp "and" Exp       	[strict, left, cons("Exp1AndSyn")]
               | Exp "or" Exp        	[strict, left, cons("Exp1OrSyn")]
               > Exp "=" Exp         	[strict(2), right, cons("Exp1AssignSyn")]

  syntax Stmt ::= "{" "}"				[cons("Stmt1BlockEmptySyn")]
                | "{" Stmts "}"			[cons("Stmt1BlockSyn")]
                | Exp ";"			  	[strict, cons("Stmt1Stmt2ExpSyn")]
                | "if" Exp "then" Stmt "else" Stmt		[prefer, strict(1), cons("Stmt1IfThnElsSyn")]
                | "if" Exp "then" Stmt					[cons("Stmt1IfThnSyn")]
                | "while" Exp "do" Stmt					[cons("Stmt1WhileSyn")]
                | "for" #Id "=" Exp "to" Exp "do" Stmt	[cons("Stmt1ForSyn")]
                | "return" Exp ";"						[strict, cons("Stmt1ReturnSyn")]
                | "return" ";"			    			[cons("Stmt1Return2Syn")]
                | "write" "(" Exp ")" ";"				[strict, cons("Stmt1WriteSyn")]
                | "try" Stmt "catch" "(" #Id ")" Stmt	[cons("Stmt1TrySyn")]
                | "throw" Exp ";"						[strict, cons("Stmt1ThrowSyn")]
                | "spawn" Stmt							[cons("Stmt1SpawnSyn")]
                | "acquire" Exp ";"                  	[strict, cons("Stmt1AcquireSyn")]
                | "release" Exp ";"                  	[strict, cons("Stmt1ReleaseSyn")]
                | "rendezvous" Exp ";"               	[strict, cons("Stmt1RendezvousSyn")]
                | "print" "(" Exps ")" ";"              [strict, cons("Stmt1PrintSyn")]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts							[right, cons("Stmts1LstStmtsSyn")]

endmodule






module SIMPLE-UNTYPED
  including SIMPLE-UNTYPED-SYNTAX

  // coming from macros
  rule if E:Exp then S:Stmt => if E then S else {}
  rule (for X:#Id = E1 to E2 do S) => {var X=E1, .Exps; while X <= E2 do {S X = (X + 1);}}
  rule var E1:Exp, E2:Exp, Es:Exps; => var E1, .Exps; var E2, Es;
  rule var X = E, .Exps; => var X, .Exps; X = E;



  syntax #Id ::= "main"

  syntax Val ::= #Int | #Bool | #String
               | "arrayRef" "(" #Int "," #Int ")" [cons("Val1ArrayRefSyn")]
               | "lambda" "(" Ids "," Stmt ")"  [cons("Val1LambdaSyn")]
  syntax Vals ::= List{Val,","} [cons("Vals1ListSyn")]
  syntax Exp ::= Val
  syntax KResult ::= Val 

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> (PGM:K ~> execute) </k>
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
                  <in color="magenta" > .List </in>
                  <out color="brown" > .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
                </T>


  syntax K ::= "undefined"  [cons("K1UndefinedSyn")]


  rule <k> var X:#Id, .Exps; => . ...</k>
       <env> Env:Map => Env[L:#Int/X] </env>
       <store>... . => L|->undefined ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>

  rule <k> var X[N:#Int, .Exps], .Exps; => . ...</k>
       <env> Env => Env:Map[L/X:#Id] </env>
       <store>... . => L |-> arrayRef(L +Int 1, N)
                       (L +Int 1) .. (L +Int N) |-> undefined ...</store>
       <nextLoc> L => (L:#Int +Int 1) +Int N </nextLoc>


  context var X:#Id[HOLE], .Exps;

  syntax #Id ::= "$1" | "$2"
  rule var X:#Id[N1:#Int,N2:#Int,Vs:Vals], .Exps; =>
       var X[N1], .Exps;
       {
         var $1 = X, .Exps;
         for $2 = 0 to N1 - 1 do   // no longer a stupid parser
         {
           var X[N2,Vs], .Exps;    // no longer a stupid parser
           $1[$2] = X;
         }
       }  [structural]

  rule <k> function F:#Id(Xs:Ids) S => . ...</k>
       <env> Env => Env[L/F] </env>
       <store>... . => L|->lambda(Xs,S) ...</store>
       <nextLoc> L => L:#Int +Int 1 </nextLoc>



  syntax K ::= "execute" [cons("K1ExecuteSyn")]
  rule <k> execute => (main(.Exps);) </k>
       <env> Env </env> <genv> . => Env </genv>  [structural]



  rule [look-up]:
       <k> X:#Id => V:Val ...</k>
       <env>...X|->L...</env>
       <store>...L|->V...</store>  [transition]



  context ++(HOLE => lvalue(HOLE))
  rule <k> ++loc(L) => I:#Int +Int 1 ...</k>
       <store>... L:#Int |-> (I => I +Int 1) ...</store>  [transition]

  rule I1:#Int + I2:#Int => I1 +Int I2
  rule Str1:#String + Str2:#String => Str1 +String Str2
  rule I1:#Int - I2:#Int => I1 -Int I2
  rule I1:#Int * I2:#Int => I1 *Int I2
  rule I1:#Int / I2:#Int => I1 /Int I2 when I2 =/=Bool 0
  rule I1:#Int % I2:#Int => I1 %Int I2 when I2 =/=Bool 0
  rule - I:#Int => -Int I
  rule I1:#Int < I2:#Int => I1 <Int I2
  rule I1:#Int <= I2:#Int => I1 <=Int I2
  rule I1:#Int > I2:#Int => I1 >Int I2
  rule I1:#Int >= I2:#Int => I1 >=Int I2
  rule V1:Val == V2:Val => V1 ==Bool V2
  rule V1:Val != V2:Val => V1 =/=Bool V2
  rule B1:#Bool and B2:#Bool => B1 andBool B2
  rule B1:#Bool or B2:#Bool => B1 orBool B2
  rule not(B:#Bool) => notBool(B)


  rule V[N1,N2,Vs] => V[N1, .Exps][N2,Vs]  [structural]
  rule arrayRef(L,_:#Int)[N] => lookup(L:#Int +Int N:#Int)  [structural]
  syntax K ::= "lookup" "(" #Int ")" [cons("K1LookupSyn")]
  rule <k> lookup(L:#Int) => V:Val ...</k> <store>...L|->V...</store>  [transition]

  rule sizeOf(arrayRef(_:#Int,N:#Int)) => N

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
  rule <k> bindto((X:#Id,Xs => Xs),(V,Vs:Vals => Vs)) ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> V:Val ...</store>
       <nextLoc> L => L:#Int +Int 1 </nextLoc>
  rule <k> bindto(.Ids,.Exps) => . ...</k>  [structural]

  rule <k> read() => I ...</k> <in> ListItem(I) => . ...</in>  [transition]


  context (HOLE => lvalue(HOLE)) = _
  rule <k> loc(L:#Int)=V:Val => V ...</k>
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


  syntax ListItem ::= "(" #Id "," Stmt "," K "," Map "," Bag ")" [cons("ListItem1ISKMBSyn")]
  syntax K ::= "popx" [cons("K1PopxSyn")]
  rule <k> (try S1 catch(X) S2 => S1 ~> popx) ~> K </k>
       <control> <xstack> . => (X:#Id,S2,K,Env,C) ...</xstack> C:Bag </control>
       <env> Env </env>
  rule <k> popx => . ...</k> <xstack> _:ListItem => . ...</xstack>
  rule <k> throw V; ~> _ => {var X:#Id=V, .Exps; S2} ~> K </k>
       <control> <xstack> (X:#Id,S2,K,Env,C) => . ...</xstack> (_ => C) </control>
       <env> _ => Env </env>


   rule <thread>... <k> spawn S => . ...</k> <env> Env </env> ...</thread>
        (. => <thread>... <k> S </k> <env> Env </env> ...</thread>)

   rule (<thread>... <k>.K</k> <holds> H:Map </holds> ...</thread> => .)
        <busy> Busy:Set => Busy -Set keys(H) </busy>


   rule <k> acquire V; => . ...</k> <holds>... . => V|->0 ...</holds>
        <busy> Busy (. => SetItem(V)) </busy>
     when (notBool(V in Busy:Set)) [transition]
   rule <k> acquire V; => . ...</k> <holds>... V:Val|->(N => N:#Int +Int 1) ...</holds>


   rule <k> release V:Val; => . ...</k>
        <holds>... V|->(N => N:#Int -Int 1) ...</holds>
     when N >Int 0
   // used prefix notation for -Int because of parsing problems
   rule <k> release V; => . ...</k> <holds>... V:Val|->0 => . ...</holds>
        <busy>... SetItem(V)=>. ...</busy>


   rule <k> rendezvous V:Val; => . ...</k>
        <k> rendezvous V; => . ...</k>  [transition]

// For parsing reasons, we prefer to allow lvalue to take a K
  syntax Exp ::= "lvalue" "(" K ")" [cons("Exp1LValueSyn")]
  syntax Val ::= "loc" "(" #Int ")" [cons("Val1LocSyn")]
// Local variable
  rule <k> lvalue(X:#Id) => loc(L:#Int) ...</k>
       <env>... X|->L ...</env>  [structural]
// Array element: evaluate the array and its index;
// then the array lookup rule above applies.
  context lvalue(_[HOLE])
  context lvalue(HOLE[_])
// Finally, return the address of the desired object member
  rule <k> lvalue(lookup(L:#Int)) => loc(L) ...</k>  [structural]



  syntax List{K} ::= #Int ".." #Int [cons("ListDlKDr1DotDotSyn")]
  rule N1:#Int..N2:#Int => .List{K}              when N1  >Int N2  [structural]
  rule N1:#Int..N2:#Int => N1 ,, (N1 +Int 1)..N2 when N1 <=Int N2  [structural]

endmodule 