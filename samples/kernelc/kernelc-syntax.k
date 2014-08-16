// Copyright (c) 2014 K Team. All Rights Reserved.

module KERNELC-SYNTAX
  syntax File ::= Globals

  syntax Global ::= FunctionDefinition
                  | FunctionDeclaration
                  | StructDeclaration
                  | "#include" "<" "stdlib.h" ">"
                  | "#include" "<" "stdio.h" ">"
  syntax Globals ::= List{Global, ""}

  syntax FunctionDefinition ::= Type Id "(" ParameterDeclarations ")" Block
  syntax FunctionDeclaration ::= Type Id "(" ParameterDeclarations ")" ";"
  syntax ParameterDeclaration ::= Type Id
  syntax ParameterDeclarations ::= List{ParameterDeclaration, ","}
  syntax StructDeclaration ::= "struct" Id "{" VariableDeclarations "}" ";"

  syntax VariableDeclaration ::= Type Id ";"
  syntax VariableDeclarations ::= List{VariableDeclaration, ""}

  syntax Type ::= IntType
                | "void"
                | Type "*"
                | "struct" Id
  syntax IntType ::= "int"

  syntax Statement ::=
      Expression "=" Expression ";"                         [strict(2)]
    | Expression ";"                                        [strict]
    | "if" "(" Expression ")" Statement "else" Statement    [avoid]
    | "if" "(" Expression ")" Statement                     [strict(1)]
    | "while" "(" Expression ")" Statement
    | "return" Expression ";"                               [strict]
    | "return" ";"
    | ";"
    | Block
  syntax Block ::= "{" VariableDeclarations Statements  "}"
  syntax Statements ::= List{Statement, ""}

  syntax Expression ::=
      Constant
    | Id
    | "(" Expression ")"                                [bracket]
    //| Expression "." Id
    | Expression "->" Id                                [strict(1)]
    | Id "(" Expressions ")"                            [strict(2)]
    //| Expression "[" Expression "]"
    > "-" Expression                                    [strict]
    | "+" Expression                                    [strict]
    | "!" Expression                                    [strict]
    | "~" Expression                                    [strict]
    | "*" Expression                                    [strict]
    | "&" Expression
    | "sizeof" "(" Type ")"
    > "(" Type ")" Expression                           [strict(2)]
    > left:
      Expression "*" Expression                         [strict]
    | Expression "/" Expression                         [strict]
    | Expression "%" Expression                         [strict]
    > left:
      Expression "+" Expression                         [strict]
    | Expression "-" Expression                         [strict]
    > left:
      Expression "<<" Expression                        [strict]
    | Expression ">>" Expression                        [strict]
    > left:
      Expression "<"  Expression                        [strict]
    | Expression "<=" Expression                        [strict]
    | Expression ">"  Expression                        [strict]
    | Expression ">=" Expression                        [strict]
    > left:
      Expression "==" Expression                        [strict]
    | Expression "!=" Expression                        [strict]
    > left: Expression "&" Expression                   [strict]
    > left: Expression "^" Expression                   [strict]
    > left: Expression "|" Expression                   [strict]
    > left: Expression "&&" Expression                  [prefer, strict(1)]
    > left: Expression "||" Expression                  [strict(1)]
    > right: Expression "?" Expression ":" Expression   [strict(1)]
  syntax Constant ::= Int
                    | "NULL"
                    | String
  syntax Expressions ::= List{Expression, ","}          [strict]

  syntax Id ::= "main"
              | "malloc"
              | "free"
              | "scanf"
              | "printf"


  /*
   * Macros
   */
  rule if (E:Expression) S:Statement => if (E) S else ;     [macro]
  rule E1:Expression || E2:Expression => (E1 ? 1 : E2)      [macro]
  rule E1:Expression && E2:Expression => (E1 ? E2 : 0)      [macro]
  rule ! E:Expression => E ? 0 : 1                          [macro]


  /*
   * Verification specific stuff
   */
  syntax Statement ::= "breakpoint"
  syntax Id ::= "find" | "insert" | "delete" | "new_node" | "find_min"
  syntax Id ::= "treeNode" | "value" | "left" | "right"
  syntax Id ::= "x" | "y" | "z" | "t" | "u" | "v" | "node" | "temp" | "min"
endmodule

