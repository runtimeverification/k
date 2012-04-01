module CHALLENGE-SYNTAX 
--- There are two main syntactic categories, Exp and Stmt

--- Basic constructs for expressions
  syntax Exp ::= Bool | Int | Float | Id

--- Basic arithmetic and boolean operations; they will work with both integers and floats
--- NOTE: can add more here
  syntax Exp ::= Exp "+" Exp   [gather(E e) prec 33 strict]       --- addition
               | Exp "*" Exp   [gather(E e) prec 31 strict]       --- multiplication
               | Exp "/" Exp   [gather(E e) prec 31 strict]       --- division
               | Exp "<=" Exp  [prec 37 latex "{#1}\leq{#2}" seqstrict]
               | Exp "==" Exp  [prec 37 strict]                   --- equality test
               | "not" Exp     [prec 53 strict]                   --- boolean negation
               | Exp "and" Exp [gather(E e) prec 55 strict(1)]    --- boolean conjunction

--- Variable declarations
  syntax Stmt ::= "var" Ids ";" [prec 2]

--- Variable assignment
  syntax Stmt ::= Exp "=" Exp ";" [prec 80 gather(e E) strict(2)]

--- Variable increment
  syntax Exp ::= "++" Id [prec 0]

--- Basic statement constructs
  syntax Stmt ::= "{" "}"
                | "{" Stmt "}"                   [gather(&)]
                | Stmt Stmt                  [prec 100 gather(e E)]
                | Exp ";"                      [prec 90 strict]
                | "if" Exp "then" Stmt "else" Stmt [strict(1)]
                | "while" Exp "do" Stmt

--- I/O
  syntax Exp ::= "read"
  syntax Stmt ::= "print" Exp ";" [strict]

--- Memory allocation and pointers
  syntax Exp ::= "&" Id
               | "*" Exp       [strict]
               | "malloc" Exp  [strict]
  syntax Stmt ::= "free" Exp ";" [strict]

--- Lists
  syntax Exp ::= "[" Exps "]" [prec 0 seqstrict hybrid]
               | Exp ":" Exp     [strict]
               | "head" Exp      [prec 0 strict]
               | "tail" Exp      [prec 0 strict]

--- Aspects
  syntax Stmt ::= "aspect" Stmt [prec 90]

--- Functions
  syntax Exp ::= "lambda" Ids "." Stmt [latex "\lambda{#1}.{#2}"]
                | Exp "(" Exps ")"     [prec 2 strict]
  syntax Stmt ::= "return" Exp ";"          [strict]

--- Fixed point
  syntax Exp ::= "mu" Id "." Exp [latex "\mu{#1}.{#2}"]

--- Callcc
  syntax Exp ::= "callcc" Exp [prec 50 strict]

--- Sequential non-determinism
  syntax Exp ::= "randomBool"

--- Threads
  syntax Stmt ::= "spawn" Stmt [prec 90]
                | "acquire" Exp ; [strict]
                | "release" Exp ; [strict]
                | "rendezvous" Exp ; [strict]

--- Agents
  syntax Exp ::= "newAgent" Stmt
               | "me"
               | "parent"
               | "receive"
               | "receiveFrom" Exp         [strict]
  syntax Stmt ::= "send" Exp "to" Exp ";"      [strict]
                | "sendSynch" Exp "to" Exp ";" [strict]
                | "barrier" ";"              --- should be "barrier;" if one wants to dissalow spaces before ;
                | "broadcast" Exp ";"        [strict]

--- Abrupt termination (of thread, of agent, of system)
  syntax Stmt ::= "haltThread" ";" | "haltAgent" ";" | "haltSystem" ";"

--- Code generation / reflection
  syntax Exp ::= "quote" Exp
               | "unquote" Exp
               | "lift" Exp    [strict]
               | "eval" Exp    [strict]

-----------------------------------------------------------------------------
--- Lists should be eventually builtin; for now, they need to be declared ---
-----------------------------------------------------------------------------
  syntax Ids ::= List{Id,","} [strict]
--- List{Exp}
  syntax Exps ::= List{Exp,","}

  macro mu X:Id.E:Exp = (lambda().{var X; X=E; return X;})()

  syntax Ids ::= "(" ")"
  macro () = .Ids
end module
