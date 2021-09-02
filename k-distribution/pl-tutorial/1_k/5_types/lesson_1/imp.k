module IMP-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Ids    ::= List{Id, ","}

  syntax AExp   ::= Int | Id | String
                  | "-" Int
                  | "++" Id
                  | "read" "(" ")"
                  | "(" AExp ")" [bracket]
                  > AExp "/" AExp [strict, left]
                  > AExp "+" AExp [strict, left]
                  > "spawn" Block [strict]
                  > Id "=" AExp [strict(2)]

  syntax AExps  ::= List{AExp, ","}
                  | Ids

  syntax BExp   ::= Bool
                  | "!" BExp [strict]
                  | "(" BExp ")" [bracket]
                  | AExp "<=" AExp [strict]
                  > BExp "&&" BExp [left, strict]

  syntax Block  ::= "{" Stmts "}"

  syntax Stmt   ::= Block
                  | AExp ";" [strict]
                  | "halt" ";"
                  | "int" Ids ";"
                  | "if" "(" BExp ")" Block "else" Block [strict]
                  | "while" "(" BExp ")" Block [strict]
                  | "print" "(" AExps ")" ";"
                  | "join" AExp ";" [strict]

  syntax Stmts  ::= List{Stmt, ""} [strict(1)]
endmodule

module IMP
  imports IMP-SYNTAX
  imports DOMAINS

  syntax BlockOrStmtType ::= "block" | "stmt"
  syntax PrintableType  ::= "int" | "string"
  syntax Type ::= PrintableType | "bool" | BlockOrStmtType

  syntax KResult  ::= Type

  syntax AExp     ::= Type
  syntax BExp     ::= Type

  configuration
    <T color="yellow">
      <k color="green"> $PGM:Stmts </k>
      <tenv color="LightSkyBlue"> .Map </tenv>
    </T>

  /* // Exp */

  rule _:Int => int
  rule _:String => string

  rule  <k> X:Id => T ...</k>
        <tenv>... X |-> T ...</tenv>

  rule  - _ => int
  rule int / int => int
  rule int + int => int
  rule string + string => string

  rule  <k> int ; => stmt ...</k>

  rule  <k> ++ X => int ...</k>
        <tenv>... X |-> int ...</tenv>

  rule _:Bool => bool
  rule ! _ => bool
  rule int <= int => bool
  rule bool && bool => bool

  /* // Stmt */
  
  rule  <k> X:Id = T => T ...</k>
        <tenv>... X |-> T ...</tenv>

  rule  <k> read() => int ...</k>

  context print(HOLE:AExp, _);

  rule  <k> print(_:PrintableType, AEs => AEs) ; ...</k>
  rule  <k> print(.AExps) ; => stmt ...</k>

  rule  <k> if ( bool ) block else block => stmt ...</k>

  rule  <k> while ( bool ) block => stmt ...</k>

  rule  <k> spawn block => int ...</k>

  rule  <k> join int ; => stmt ...</k>

  rule  <k> halt ; => stmt ...</k>

  /* // Block */

  syntax Block  ::= Type

  rule  <k> .Stmts => stmt:KItem       ...</k> [structural]
  rule  <k> _:BlockOrStmtType Ss => Ss ...</k>

  rule  <k> { S } => S ~> Rho ...</k>
        <tenv> Rho </tenv> [structural]

  rule  <k> _:BlockOrStmtType ~> Rho => block ...</k>
        <tenv> _ => Rho </tenv> [structural]

  /* // Pgm */

  rule  <k> int (X:Id, Xs:Ids => Xs) ;  ...</k>
        <tenv> M => M[X <- int]  </tenv>

  rule  <k> int .Ids ; => stmt ...</k>

endmodule
