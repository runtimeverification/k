// Copyright (c) 2014-2015 K Team. All Rights Reserved.

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
                | FloatType
                | "void"
                | Type "*"
                | "struct" Id
  syntax IntType ::= "int"
  syntax FloatType ::= "double"

  syntax Statement ::=
      Expression "=" Expression ";"                         [seqstrict(2)]
    | Expression ";"                                        [seqstrict]
    | "if" "(" Expression ")" Statement "else" Statement    [avoid]
    | "if" "(" Expression ")" Statement
    | "while" "(" Expression ")" Statement
    | "return" Expression ";"                               [seqstrict]
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
    | Expression "->" Id
    | Id "(" Expressions ")"                            [seqstrict(2)]
    //| Expression "[" Expression "]"
    > "-" Expression                                    [seqstrict]
    | "+" Expression                                    [seqstrict]
    | "!" Expression                                    [seqstrict]
    | "~" Expression                                    [seqstrict]
    | "*" Expression                                    [seqstrict]
    | "&" Expression
    | "sizeof" "(" Type ")"
    > "(" Type ")" Expression                           [seqstrict(2)]
    > left:
      Expression "*" Expression                         [seqstrict]
    | Expression "/" Expression                         [seqstrict]
    | Expression "%" Expression                         [seqstrict]
    > left:
      Expression "+" Expression                         [seqstrict]
    | Expression "-" Expression                         [seqstrict]
    > left:
      Expression "<<" Expression                        [seqstrict]
    | Expression ">>" Expression                        [seqstrict]
    > left:
      Expression "<"  Expression                        [seqstrict]
    | Expression "<=" Expression                        [seqstrict]
    | Expression ">"  Expression                        [seqstrict]
    | Expression ">=" Expression                        [seqstrict]
    > left:
      Expression "==" Expression                        [seqstrict]
    | Expression "!=" Expression                        [seqstrict]
    > left: Expression "&" Expression                   [seqstrict]
    > left: Expression "^" Expression                   [seqstrict]
    > left: Expression "|" Expression                   [seqstrict]
    > left: Expression "&&" Expression                  [prefer, seqstrict(1)]
    > left: Expression "||" Expression                  [seqstrict(1)]
    > right: Expression "?" Expression ":" Expression
  syntax Constant ::= Int
                    | Float
                    | "NULL"
                    | String
  syntax Expressions ::= List{Expression, ","}          [seqstrict]

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
  syntax Id ::= "find" | "insert" | "delete" | "new_node" | "find_min" | "max" | "update_height"
              | "average" | "minimum" | "maximum" | "multiplication_by_addition" | "comm_assoc"
              | "left_rotate" | "right_rotate" | "balance"
              | "head" | "tail" | "add" | "swap" | "deallocate" | "length_recursive" | "length_iterative" | "sum_recursive" | "sum_iterative" | "reverse" | "append" | "copy" | "filter"
              | "height" | "compute_size" | "mirror" | "inorder" | "preorder" | "postorder" | "iter_deallocate" | "tree_to_list_iterative" | "tree_to_list_recursive"
              | "quicksort" | "merge_sort" | "bubble_sort" | "insertion_sort"
  syntax Id ::= "listNode" | "stackNode" | "val" | "next"
  syntax Id ::= "treeNode" | "node" | "value" | "left" | "right"
  syntax Id ::= "sqs" | "sqv" | "dot" | "tau_vv" | "horizontal_los" | "omega_vv" | "cd2d"
  syntax Id ::= "a" | "b" | "c" | "x" | "y" | "z" | "t" | "u" | "v" | "p" | "n" | "s" | "l" | "ln" | "tn" | "sn" | "temp" | "min" | "iterx" | "itery" | "change"
endmodule
