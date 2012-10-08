module IMP-SYNTAX
  syntax AExp  ::= Int | Id | String
                 | "++" Id
                 | "read" "(" ")"
                 > AExp "/" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [strict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict]
                 | "while" "(" BExp ")" Block [strict]
                 | "int" Ids ";"
                 | "print" "(" AExps ")" ";"  [strict]
                 | "halt" ";"
                 > "spawn" Stmt               [strict]
                 > Stmt Stmt                  [left,seqstrict]

  syntax Ids   ::= List{Id,","}               [strict]
  syntax AExps ::= List{AExp,","}             [strict]
endmodule


module IMP
  imports IMP-SYNTAX
  syntax BlockOrStmtType ::= "block" | "stmt"
  syntax PrintableType  ::= "int" | "string"
  syntax Type ::= PrintableType | "bool" | BlockOrStmtType
  syntax KResult ::= Type

  configuration <T color="yellow">
                  <k color="green"> $PGM:Stmt </k>
                  <tenv color="LightSkyBlue"> .Map </tenv>
                </T>

// AExp
  rule _:Int => int
  rule _:String => string
  rule <k>   X:Id => T ...</k> <tenv>... X |-> T ...</tenv>
  rule <k> ++X:Id => int ...</k> <tenv>... X |-> int ...</tenv>
  rule read() => int

  syntax AExp ::= Type
  rule int / int => int
  rule int + int => int
  rule string + string => string
// BExp
  syntax BExp ::= Type
  rule _:Bool => bool
  rule int <= int => bool
  rule ! bool => bool
  rule bool && bool => bool
// Block
  rule {} => block
  rule <k> {S} => S ~> tenv(Rho) ...</k> <tenv> Rho </tenv>
  syntax K ::= tenv(Map)
  rule <k> _:BlockOrStmtType ~> tenv(Rho) => block ...</k>
       <tenv> _ => Rho </tenv>
// Stmt
  rule <k> X = T; => stmt ...</k> <tenv>... X |-> T ...</env>

  rule _:BlockOrStmtType _:BlockOrStmtType => stmt

  syntax Block ::= Type
  rule if (bool) block else block => stmt
  rule while (bool) block => stmt

  rule <k> int (X:Id,Xs:Ids => Xs); ...</k> <tenv>... . => X |-> int ...</env>
  rule int .Ids; => stmt

  rule print(_:PrintableType,AEs => AEs);
  rule print(.AExps); => stmt
  
  rule halt; => stmt
  rule spawn stmt => stmt
endmodule
