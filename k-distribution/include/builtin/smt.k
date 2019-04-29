module SMTLIB2-SYNTAX
  imports SMTLIB2
  syntax SMTLIB2SimpleSymbol ::= r"(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*" [prec(1), notInRules, token, autoReject]
  syntax SMTLIB2Identifier ::= "(" "_" SMTLIB2Symbol SMTLIB2IndexList ")" [klabel(indexedIdentifier)]
endmodule

module SMTLIB2
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports STRING
  imports K-IO

// Tokens
  syntax SMTLIB2Numeral ::= Int
  syntax SMTLIB2SimpleSymbol ::= Bool
  syntax SMTLIB2Symbol ::= SMTLIB2SimpleSymbol

// S Expressions
  syntax SMTLIB2SpecConstant ::= SMTLIB2Numeral
  syntax SMTLIB2SExpr ::= SMTLIB2SpecConstant
                        | SMTLIB2Symbol
                        | "(" SMTLIB2SExprList ")"
  syntax SMTLIB2SExprList ::= List{SMTLIB2SExpr, ""} [klabel(SMTLIB2SExprList)]

// Identifiers
  syntax SMTLIB2Index      ::= SMTLIB2Numeral | SMTLIB2Symbol
  syntax SMTLIB2IndexList  ::= List{SMTLIB2Index, ""} [klabel(SMTLIB2IndexList)]
  syntax SMTLIB2Identifier ::= SMTLIB2Symbol
                             | "(" "underscore" SMTLIB2Symbol SMTLIB2IndexList ")" [klabel(indexedIdentifier)]

// Sorts
  syntax SMTLIB2Sort ::= SMTLIB2Identifier
                       | "(" SMTLIB2Identifier SMTLIB2SortList ")"
  syntax SMTLIB2SortList ::= List{SMTLIB2Sort, ""} [klabel(SMTLIB2SortList)]

// Terms
  syntax SMTLIB2QualIdentifier ::= SMTLIB2Identifier
                                 | "(" "as" SMTLIB2Identifier SMTLIB2Sort ")"
  syntax SMTLIB2SortedVar ::= "(" SMTLIB2Symbol SMTLIB2Sort ")"
  syntax SMTLIB2SortedVarList ::= List{SMTLIB2SortedVar, ""} [klabel(SMTLIB2SortedVarList)]
  syntax SMTLIB2Term ::= SMTLIB2SpecConstant
                       | SMTLIB2QualIdentifier
                       | "(" SMTLIB2QualIdentifier SMTLIB2TermList ")"
                       | "(" "forall" "(" SMTLIB2SortedVarList ")" SMTLIB2Term ")"
                       | "(" "exists" "(" SMTLIB2SortedVarList ")" SMTLIB2Term ")"
  syntax SMTLIB2TermList ::= List{SMTLIB2Term, ""} [klabel(SMTLIB2TermList)]

// Commands
  syntax SMTLIB2Command ::= "(" "assert"        SMTLIB2Term               ")"
                          | "(" "declare-const" SMTLIB2Symbol SMTLIB2Sort ")"
                          | "(" "declare-fun"   SMTLIB2Symbol "(" SMTLIB2SortList ")" SMTLIB2Sort ")"
                          | "(" "define-fun"    SMTLIB2Symbol "(" SMTLIB2SortedVarList ")" SMTLIB2Sort SMTLIB2Term ")"
                          | "(" "define-sort"   SMTLIB2Symbol "(" SMTLIB2SortList ")" SMTLIB2Sort ")"
  syntax SMTLIB2Script ::= List{SMTLIB2Command, ""} [klabel(SMTLIB2Script)]


  // Core symbols
  syntax SMTLIB2SimpleSymbol ::= "not"   [token]
                               | "or"    [token]
                               | "and"   [token]
                               | "="     [token]

  // Arithmetic
  syntax SMTLIB2SimpleSymbol ::= "*"     [token]
                               | "+"     [token]
                               | "/"     [token]
                               | "-"     [token]
                               | "^"     [token]
                               | ">"     [token]
                               | "<"     [token]

  // Sets (defined by CVC4, but not Z3)
  syntax SMTLIB2SimpleSymbol ::= "emptyset"     [token]
                               | "singleton"    [token]
                               | "union"        [token]
                               | "intersection" [token]
                               | "member"       [token]

  // Extensional Arrays
  syntax SMTLIB2SimpleSymbol ::= "select" [token]
                               | "store"  [token]
                               | "map"    [token]

  // Sorts
  syntax SMTLIB2SimpleSymbol ::= "Int" [token] | "Bool" [token]
                               | "Set" [token] | "Array" [token]

  syntax CheckSATResult ::= "sat" | "unsat" | "unknown" "(" K ")"
                          | "error" "(" K ")"


// Concatenation:

  syntax SMTLIB2Script ::= SMTLIB2Script "++SMTLIB2Script" SMTLIB2Script [function, right]
  rule (COMMAND:SMTLIB2Command SCRIPT1:SMTLIB2Script) ++SMTLIB2Script SCRIPT2:SMTLIB2Script
    => COMMAND (SCRIPT1 ++SMTLIB2Script SCRIPT2)
  rule .SMTLIB2Script ++SMTLIB2Script SCRIPT2 => SCRIPT2


// Serialize to String:

  syntax String ::= SMTLIB2NumeralToString(SMTLIB2Numeral) [function]
  rule SMTLIB2NumeralToString(I:Int) => Int2String(I)

  syntax String ::= SMTLIB2SimpleSymbolToString(SMTLIB2SimpleSymbol)   [function, functional, hook(STRING.token2string)]
  rule SMTLIB2SimpleSymbolToString(true)  => "true"
  rule SMTLIB2SimpleSymbolToString(false) => "false"

  syntax String ::= SMTLIB2IndexToString(SMTLIB2Index)             [function]
  rule SMTLIB2IndexToString(I:SMTLIB2Numeral) => SMTLIB2TermToString(I)
  rule SMTLIB2IndexToString(I:SMTLIB2Symbol)  => SMTLIB2TermToString(I)

  syntax String ::= SMTLIB2IndexListToString(SMTLIB2IndexList)         [function]
  rule SMTLIB2IndexListToString( I Is )
    => SMTLIB2IndexToString(I) +String " " +String SMTLIB2IndexListToString(Is)
  rule SMTLIB2IndexListToString( .SMTLIB2IndexList ) => ""

  syntax String ::= SMTLIB2TermToString(SMTLIB2Term)         [function]
  rule SMTLIB2TermToString( N:SMTLIB2Numeral ) => SMTLIB2NumeralToString(N)
  rule SMTLIB2TermToString( Op:SMTLIB2SimpleSymbol ) => SMTLIB2SimpleSymbolToString( Op )
  rule SMTLIB2TermToString( ( ID:SMTLIB2QualIdentifier Ts ) )
    => "(" +String SMTLIB2TermToString(ID) +String " " +String SMTLIB2TermListToString(Ts) +String ")"
  rule SMTLIB2TermToString( ( as ID SORT ) )
    => "( as " +String SMTLIB2TermToString(ID) +String " " +String SMTLIB2SortToString(SORT) +String ")"
  rule SMTLIB2TermToString( ( underscore SYMBOL INDICES ) )
    => "( _ " +String SMTLIB2TermToString(SYMBOL) +String " " +String
                      SMTLIB2IndexListToString(INDICES) +String
       ")"
  rule SMTLIB2TermToString( (forall (Vs)  T) )
    => "( forall (" +String SMTLIB2SortedVarListToString(Vs) +String ") " +String
                 SMTLIB2TermListToString(T)  +String
       ") "

  syntax String ::= SMTLIB2TermListToString(SMTLIB2TermList)         [function]
  rule SMTLIB2TermListToString( T Ts )
    => SMTLIB2TermToString(T) +String " " +String SMTLIB2TermListToString(Ts)
  rule SMTLIB2TermListToString( .SMTLIB2TermList ) => ""

  syntax String ::= SMTLIB2SortToString(SMTLIB2Sort)         [function]
  rule SMTLIB2SortToString( S:SMTLIB2SimpleSymbol ) => SMTLIB2SimpleSymbolToString(S)
  rule SMTLIB2SortToString( ( Set S ) )
    => "( Set " +String SMTLIB2SortToString(S) +String " )"
  rule SMTLIB2SortToString( ( Array S1 S2 ) )
    => "( Array " +String SMTLIB2SortToString(S1) +String " " +String SMTLIB2SortToString(S2) +String " )"

  syntax String ::= SMTLIB2SortListToString(SMTLIB2SortList) [function]
  rule SMTLIB2SortListToString( S Ss )
    => SMTLIB2SortToString(S) +String " " +String SMTLIB2SortListToString(Ss)
  rule SMTLIB2SortListToString( .SMTLIB2SortList ) => ""

  syntax String ::= SMTLIB2SortedVarListToString(SMTLIB2SortedVarList) [function]
  rule SMTLIB2SortedVarListToString( S Ss )
    => SMTLIB2SortedVarToString(S) +String " " +String SMTLIB2SortedVarListToString(Ss)
  rule SMTLIB2SortedVarListToString( .SMTLIB2SortedVarList ) => ""

  syntax String ::= SMTLIB2SortedVarToString(SMTLIB2SortedVar) [function]
  rule SMTLIB2SortedVarToString( (V S) )
    => "(" +String
           SMTLIB2TermToString( V ) +String " " +String SMTLIB2SortToString( S ) +String
       ")"

  syntax String ::= SMTLIB2CommandToString(SMTLIB2Command)   [function]
  rule SMTLIB2CommandToString( ( declare-const SYMBOL SORT ) )
    => "( declare-const " +String SMTLIB2TermToString(SYMBOL) +String " " +String SMTLIB2SortToString(SORT) +String ")"
  rule SMTLIB2CommandToString( ( declare-fun SYMBOL (ARGS) RET ) )
    => "( declare-fun " +String SMTLIB2TermToString(SYMBOL) +String
       " ( " +String SMTLIB2SortListToString(ARGS) +String " ) "
       +String SMTLIB2SortToString(RET) +String
       ")"
  rule SMTLIB2CommandToString( ( define-fun SYMBOL (ARGS) RET BODY) )
    => "( define-fun " +String SMTLIB2TermToString(SYMBOL) +String
       " ( " +String SMTLIB2SortedVarListToString(ARGS) +String
       " ) " +String
       SMTLIB2SortToString(RET) +String
       SMTLIB2TermToString(BODY) +String
       ")"
  rule SMTLIB2CommandToString( ( define-sort NAME (PARAMS) BODY) )
    => "( define-sort " +String SMTLIB2TermToString(NAME) +String
       " ( " +String SMTLIB2SortListToString(PARAMS) +String
       " ) " +String
       SMTLIB2SortToString(BODY) +String
       " ) "
  rule SMTLIB2CommandToString( ( assert TERM ) )
    => "( assert " +String SMTLIB2TermToString(TERM) +String ")"

  syntax String ::= SMTLIB2ScriptToString(SMTLIB2Script)     [function]
  rule SMTLIB2ScriptToString( .SMTLIB2Script ) => ""
  rule SMTLIB2ScriptToString( COMMAND SCRIPT )
    => SMTLIB2CommandToString( COMMAND ) +String "\n" +String SMTLIB2ScriptToString( SCRIPT )

  syntax CheckSATResult ::= CheckSATHelper(/*Query*/String, String/*Command*/) [function]
  syntax CheckSATResult ::= "CheckSAT.doWrite"  "(" /*Query*/String "," /*Command*/String "," IOFile ")"       [function]
  syntax CheckSATResult ::= "CheckSAT.doClose"  "(" /*Query*/String "," /*Command*/String "," IOFile "," K ")" [function]
  syntax CheckSATResult ::= "CheckSAT.doSystem" "(" /*Query*/String "," /*Command*/String "," String "," K ")" [function]
  rule CheckSATHelper(Q, C)
    => CheckSAT.doWrite(Q, C, #mkstemp("query", ".smt"))
  rule CheckSAT.doWrite(Q, C, #tempFile(FN, FD))
    => CheckSAT.doClose(Q, C, #tempFile(FN, FD), #write(FD, Q))
  rule CheckSAT.doClose(Q, C, #tempFile(FN, FD), .K)
    => CheckSAT.doSystem(Q, C, FN, #close(FD))
  rule CheckSAT.doSystem(Q, C, FN, .K) => CheckSAT.parseResult(#system(C +String FN))

  rule CheckSAT.doWrite(_, C, E:IOError) => error(E)
  rule CheckSAT.parseResult(#systemResult(I, STDOUT, STDERR))
    => error(#systemResult(I, STDOUT, STDERR))
    requires I =/=Int 0

  syntax CheckSATResult ::= "CheckSAT.parseResult" "(" KItem ")" [function]
  rule CheckSAT.parseResult(#systemResult(0, "sat\n", STDERR))     => sat
  rule CheckSAT.parseResult(#systemResult(0, "unsat\n", STDERR))   => unsat
  rule CheckSAT.parseResult(#systemResult(0, "unknown\n", STDERR)) => unknown(.K)
endmodule

module Z3
  imports SMTLIB2
  syntax CheckSATResult ::= Z3CheckSAT(SMTLIB2Script) [function]
  rule Z3CheckSAT(QUERY)
    => CheckSATHelper( SMTLIB2ScriptToString(QUERY) +String "\n( check-sat )\n", "z3 ")
endmodule

module CVC4
  imports SMTLIB2
  syntax CheckSATResult ::= CVC4CheckSAT(SMTLIB2Script) [function]
  rule CVC4CheckSAT(QUERY)
    => CheckSATHelper( "( set-logic ALL_SUPPORTED ) \n "
               +String SMTLIB2ScriptToString(QUERY)
               +String "\n( check-sat )\n"
                     , "cvc4 --lang smt "
                     )
endmodule

