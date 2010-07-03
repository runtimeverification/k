kmod AGENT-SYNTAX is including PL-INT + BOUNDING-EXP-SYNTAX

--- Basic constructs for expressions
  syntax Exp ::= Bool | Int 

--- Basic arithmetic and boolean operations; they will work with both integers and floats
--- NOTE: can add more here
  syntax Exp ::= Exp + Exp   [gather(E e) prec 33 strict]       --- addition
               | Exp * Exp   [gather(E e) prec 31 strict]       --- multiplication
               | Exp / Exp   [gather(E e) prec 31 strict]       --- division
               | Exp <= Exp  [prec 37 latex "{#1}\leq{#2}" seqstrict]
               | Exp == Exp  [prec 37 strict]                   --- equality test
               | not Exp     [prec 53 strict]                   --- boolean negation
               | Exp and Exp [gather(E e) prec 55 strict(1)]    --- boolean conjunction

--- Basic statement constructs
  syntax Exp ::= skip
               | Exp ; Exp                  [prec 100 gather(e E) strict(1)]
               | if Exp then Exp else Exp   [strict(1)]
               | while Exp do Exp

--- I/O
  syntax Exp ::= read
  syntax Exp ::= print Exp [strict]

--- Functions
  syntax Exp ::= lambda BoundingExp [prec 110 latex "\lambda{#1}"]
               | Exp Exp  [strict]

--- Fixed point
  syntax Exp ::= mu BoundingExp [prec 110 latex "\mu{#1}"]

--- Callcc
  syntax Exp ::= callcc Exp [prec 50 strict]

--- Threads
  syntax Exp ::= spawn Exp       [prec 90]
               | acquire Exp     [strict]
               | release Exp     [strict]
               | rendezvous Exp  [strict]

--- Agents
  syntax Exp ::= newAgent Exp
               | me
               | parent
               | receive
               | receiveFrom Exp       [strict]
  syntax Exp ::= send Exp to Exp       [strict]
               | sendSynch Exp to Exp  [strict]
               | barrier        
               | broadcast Exp         [strict]

--- Abrupt termination (of thread, of agent, of system)
  syntax Exp ::= haltThread | haltAgent | haltSystem

--- Additional unnecessary operators
endkm

