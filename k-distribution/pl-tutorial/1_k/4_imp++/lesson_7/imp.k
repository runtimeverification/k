module IMP-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Ids    ::= List{Id, ","}

  syntax AExp   ::= Int | Id | String
                  | "-" Int
                  | "++" Id
                  | "read" "(" ")"
                  | "(" AExp ")" [bracket]
                  > AExp "/" AExp [strict, left, division]
                  > AExp "+" AExp [strict, left]
                  > "spawn" Block
                  > Id "=" AExp [strict(2)]

  syntax AExps  ::= List{AExp, ","}
                  | Ids

  syntax BExp   ::= Bool
                  | "!" BExp [strict]
                  | "(" BExp ")" [bracket]
                  | AExp "<=" AExp [seqstrict]
                  > BExp "&&" BExp [strict(1)]

  syntax Block  ::= "{" Stmts "}"

  syntax Stmt   ::= Block
                  | AExp ";" [strict]
                  | "halt" ";"
                  | "int" Ids ";"
                  | "if" "(" BExp ")" Block "else" Block [strict(1)]
                  | "while" "(" BExp ")" Block
                  | "print" "(" AExps ")" ";"
                  | "join" AExp ";" [strict]

  syntax Stmts  ::= List{Stmt, ""}
endmodule

module IMP
  imports IMP-SYNTAX
  imports DOMAINS

  syntax KResult ::= Int | Bool | String

  configuration
    <T color="yellow">
      <threads color="orange">
        <thread multiplicity="*" color="blue" type="Map">
          <id color="Salmon"> 0 </id>
          <k color="green"> $PGM:Stmts </k>
          <env color="LightSkyBlue"> .Map </env>
        </thread>
      </threads>
      <store color="red"> .Map </store>
      <input color="magenta" stream="stdin"> .List </input>
      <output color="Orchid" stream="stdout"> .List </output>
      <done color="brown"> .Set </done>
    </T>

  // Exp

  rule  <k> X:Id => I ...</k>
        <env>... X |-> N ...</env>
        <store>... N |-> I ...</store>
        [lookup]

  rule  - I => 0 -Int I
  rule I1 / I2 => I1 /Int I2 requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule S1 + S2 => S1 +String S2

  rule  <k> _:Int ; => . ...</k>

  rule  <k> ++ X => I +Int 1 ...</k>
        <env>... X |-> N ...</env>
        <store>... N |-> (I => I +Int 1) ...</store>
        [increment]

  rule ! B => notBool B
  rule I1 <= I2 => I1 <=Int I2
  rule true && B2 => B2
  rule false && _ => false

  // Stmt
  
  rule  <k> X:Id = I:Int => I ...</k>
        <env>... X |-> N ...</env>
        <store>... N |-> (_ => I) ...</store>
        [assignment]

  rule  <k> read() => I ...</k>
        <input> ListItem(I:Int) => .List ...</input>
        [read]

  context print(HOLE:AExp, _);

  syntax Printable  ::= Int | String
  syntax AExp       ::= Printable

  rule  <k> print(P:Printable, AEs => AEs) ; ...</k>
        <output>... .List => ListItem(P) </output>
        [print]

  rule  <k> print(.AExps) ; => . ...</k>

  rule  <k> if ( true  ) B else _ => B ...</k>
  rule  <k> if ( false ) _ else B => B ...</k>

  rule  <k> while (C) B => if (C) { B while (C) B } else { .Stmts } ...</k>
        [structural]

  rule  <k> spawn S => !I ...</k>
        <env> Rho </env>
        (.Bag =>
          <thread> 
            ...
            <id> !I:Int </id>
            <k> S </k>
            <env> Rho </env>
            ...
          </thread>)

  rule  (<thread>... <id> I </id> <k> . </k> ...</thread> => .Bag) 
        <done>... .Set => SetItem(I) ...</done> [structural]

  rule  <k> join I:Int ; => . ...</k>
        <done>... SetItem(I) ...</done>

  rule  <k> halt ; ~> _ => . </k>

  rule  <k> S:Stmt S':Stmt => S ~> S' ...</k>

  // Block

  rule  <k> .Stmts => .       ...</k> [structural]
  rule  <k> S:Stmt Ss:Stmts => S ~> Ss ...</k> [structural]

  rule  <k> { S } => S ~> Rho ...</k>
        <env> Rho </env> [structural]

  rule  <k> Rho => . ...</k>
        <env> _ => Rho </env> [structural]

  // Pgm

  rule  <k> int (X, Xs => Xs) ;  ...</k>
        <env> Rho => Rho [X <- !N:Int] </env>
        <store>... .Map => !N |-> 0 ...</store>

  rule  <k> int .Ids ; => . ...</k>
endmodule
