// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module KERNELC-COMMON-SYNTAX
  imports BOOL-SYNTAX
  imports INT-SYNTAX
  imports FLOAT-SYNTAX
  imports STRING-SYNTAX
  imports EMPTY-ID

  syntax File ::= Globals

  syntax Global ::= FunctionDefinition
                  | FunctionDeclaration
                  | StructDeclaration
                  | "#include" "<" "stdlib.h" ">"
                  | "#include" "<" "stdio.h" ">"
  syntax Globals ::= List{Global, ""}   [klabel(_Globals_)]

  syntax FunctionDefinition ::= Type Id "(" ParameterDeclarations ")" Block
  syntax FunctionDeclaration ::= Type Id "(" ParameterDeclarations ")" ";"
  syntax ParameterDeclaration ::= Type Id
  syntax ParameterDeclarations ::= List{ParameterDeclaration, ","}
    [klabel(_ParameterDeclarations_)]
  syntax StructDeclaration ::= "struct" Id "{" VariableDeclarations "}" ";"

  syntax VariableDeclaration ::= Type Id ";"
  syntax VariableDeclarations ::= List{VariableDeclaration, ""}
    [klabel(_VariableDeclarations_)]

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
    > "(" Type ")" Expression
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

  syntax Id ::= "main"   [token]
              | "malloc" [token]
              | "free"   [token]
              | "scanf"  [token]
              | "printf" [token]


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
  syntax Id ::= "find" [token] | "insert" [token] | "delete" [token] | "new_node" [token] | "find_min" [token] | "max" [token] | "update_height" [token]
              | "average" [token] | "minimum" [token] | "maximum" [token] | "multiplication_by_addition" [token] | "comm_assoc" [token]
              | "left_rotate" [token] | "right_rotate" [token] | "balance" [token]
              | "head" [token] | "tail" [token] | "add" [token] | "swap" [token] | "deallocate" [token] | "length_recursive" [token]
              | "length_iterative" [token] | "sum_recursive" [token] | "sum_iterative" [token] | "reverse" [token] | "append" [token]
              | "copy" [token] | "filter" [token] | "height" [token] | "compute_size" [token] | "mirror" [token] | "inorder" [token]
              | "preorder" [token] | "postorder" [token] | "iter_deallocate" [token] | "tree_to_list_iterative" [token] | "tree_to_list_recursive" [token]
              | "quicksort" [token] | "merge_sort" [token] | "bubble_sort" [token] | "insertion_sort" [token]
  syntax Id ::= "listNode" [token] | "stackNode" [token] | "val" [token] | "next" [token]
  syntax Id ::= "treeNode" [token] | "node" [token] | "value" [token] | "left" [token] | "right" [token]
  syntax Id ::= "sqs" [token] | "sqv" [token] | "dot" [token] | "tau_vv" [token] | "horizontal_los" [token] | "omega_vv" [token] | "cd2d" [token]
  syntax Id ::= "a" [token] | "b" [token] | "c" [token] | "x" [token] | "y" [token] | "z" [token] | "t" [token] | "u" [token] | "v" [token]
              | "p" [token] | "n" [token] | "s" [token] | "l" [token] | "ln" [token] | "tn" [token] | "sn" [token] | "temp" [token]
              | "min" [token] | "iterx" [token] | "itery" [token] | "change" [token]
endmodule

module KERNELC-SYNTAX
  imports KERNELC-COMMON-SYNTAX
  imports ID
endmodule

