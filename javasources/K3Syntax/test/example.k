
module EXAMPLE-SYNTAX

  syntax A ::= a(X) [a]
  syntax B ::= "a" "(" X ")" [a]
  
  
  syntax Start ::= Stmts
  syntax Ids ::= List{Id,","} [strict, cons("Ids1ListSyn"), hybrid]
  syntax Exps ::=  List{Exp,","} [cons("Exps1ListSyn")]


  syntax Decl ::= "var" Exps ";" [cons("Ddecl1VarDeclSyn")]
                | "function" Id "(" Ids ")" Stmt [cons("Ddecl1FuncDeclSyn")]

  syntax Exp ::= Int | Bool | Id | String
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
                | "if" Exp "then" Stmt "else" Stmt		[avoid, strict(1), cons("Stmt1IfThnElsSyn")]
                | "if" Exp "then" Stmt					[cons("Stmt1IfThnSyn")]
                | "while" Exp "do" Stmt					[cons("Stmt1WhileSyn")]
                | "for" Id "=" Exp "to" Exp "do" Stmt	[cons("Stmt1ForSyn")]
                | "write" "(" Exp ")" ";"				[strict, cons("Stmt1WriteSyn")]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts							[right, cons("Stmts1LstStmtsSyn")]

endmodule




module EXAMPLE
   imports EXAMPLE-SYNTAX

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> $PGM:K </k>
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

  syntax Val ::= Int | Bool | String
               | "arrayRef" "(" Int "," Int ")" [cons("Val1ArrayRefSyn")]
               | "lambda" "(" Ids "," Stmt ")"  [cons("Val1LambdaSyn")]
  syntax Vals ::= List{Val,","} [cons("Vals1ListSyn")]
  syntax Exp ::= Val
  syntax KResult ::= Val
  syntax K ::= "undefined"  [cons("K1UndefinedSyn")]
  syntax List{K} ::= Int ".." Int [cons("ListDlKDr1DotDotSyn")]
  syntax K ::= "bindto" "(" Ids "," Vals ")" [cons("K1BindToSyn")]


  rule {S X = (X + 1);} //74
  rule var X; X = E; // 76
  rule <k> var X:Id; => . ...</k>
       <env> Env:Map => Env[L:Int/X] </env>
       <store>... . => L|->undefined ...</store>
       <nextLoc> L => L +Int 1 </nextLoc> // 112

  rule <k> var X[N:Int]; => . ...</k>
       <env> Env => Env:Map[L/X:Id] </env>
       <store>... . => L |-> arrayRef(L +Int 1, N)
                       (L +Int 1) .. (L +Int N) |-> undefined ...</store>
       <nextLoc> L => (L:Int +Int 1) +Int N </nextLoc> // 117
       
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
       }  [structural] // 127

  rule <k> function F:Id(Xs:Ids) S => . ...</k>
       <env> Env => Env[L/F] </env>
       <store>... . => L|->lambda(Xs,S) ...</store>
       <nextLoc> L => L:Int +Int 1 </nextLoc> // 138
       
  rule <k> bindto((X:Id,Xs => Xs),(V,Vs:Vals => Vs)) ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> V:Val ...</store>
       <nextLoc> L => L:Int +Int 1 </nextLoc> // 203
       
   rule (<thread>... <k>.K</k> <holds> H:Map </holds> ...</thread> => .)
        <busy> Busy:Set => Busy -Set keys(H) </busy> // 256




endmodule

