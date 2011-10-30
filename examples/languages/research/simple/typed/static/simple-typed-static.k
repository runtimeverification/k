----------------------------------
--- SIMPLE-TYPED-SYNTAX module ---
----------------------------------

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
               | "++" Exp              [:prec 0:]
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
               | Exp "=" Exp           [:strict(2) prec(40)  gather (e E):]
               | Exp ":" Type          [:prec(10):]
                                       // allowed only for declarations
  syntax Exps ::= List{Exp,","}

  syntax Stmt ::= "{" "}"
                | "{" Stmts "}
                | Exp ";"                               [:strict prec(45):]
                | "if" Exp "then" Stmt "else" Stmt      [:strict(1) prec(90):]
                | "if" Exp "then" Stmt                  [:prec(89):]
                | "while" Exp "do" Stmt                 [:strict prec(90):]
                | "for" #Id "=" Exp "to" Exp "do" Stmt  [:prec(90):]
                | "return" Exp ";"                      [:strict:]
                | "return" ";"
                | "print" "(" Exps ")" ";"              [:strict:]
                | "try" Stmt "catch" "(" #Id ")" Stmt   [:prec(90):]
                | "throw" Exp ";"                       [:strict:]
                | "spawn" Stmt                          [:strict prec(90):]
                | "acquire" Exp ";"                     [:strict:]
                | "release" Exp ";"                     [:strict:]
                | "rendezvous" Exp ";"                  [:strict:]

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
                   <return multiplicity="?"> .K </return>
                   <tasks color="blue" multiplicity="?">
                     <task multiplicity="*">
                       <code> .K </code>
                       <type> .K </type>
                     </task>
                   </tasks>
                   <pass> 1st </pass>
                </T>

  syntax Type ::= "stmt"

// empty list of variable declarations when functions with no arguments
---  rule var; => .K   [: structural:]

  rule <k> var X:#Id : T:Type; => stmt ...</k>
       <tenv> Rho:Map => Rho[T/X] </tenv>

  context var X[[HOLE]] : array of T;
  rule <k> var X[int] : array of T; => stmt ...</k>
       <tenv> Rho => Rho[array of T / X] </tenv>

  rule <k> function X(XTs:Exps) : T S:Stmt => stmt ...</k>
       <tenv> Rho => Rho[function from types(XTs) to T / X] </tenv>
       <pass> 1st </pass>
       (. => <task> <code> {var XTs; S} </code> <type> T </type> </task>)

// report: . instead of .K
  rule <k> stmt </k> <pass> 1st => 2nd </pass>

  rule <k> stmt => S </k> <pass> 2nd </pass> <return> _ => T </return>
       (<task> <code> S </code> <type> T </type> </task> => .)


  rule stmt stmt => stmt

  syntax Types ::= "types" "(" Exps ")"    [:prec(1):]
  rule types() => .Types                   [:structural:]
  rule types(X : T, XTs) => T, types(XTs)  [:structural:]

end module
