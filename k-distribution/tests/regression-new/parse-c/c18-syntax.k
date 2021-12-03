module C-LEXICAL-SORTS
  syntax Identifier
  syntax Constant ::= Char
  syntax StringLiteral
  syntax Char
endmodule

module C-LEXICAL
  imports C-LEXICAL-SORTS

  imports ID-SYNTAX
  imports FLOAT-SYNTAX
  imports STRING-SYNTAX

  syntax Identifier ::= Id
  syntax Constant ::= IntConstant | Float
  syntax StringLiteral ::= String

  syntax IntConstant ::= r"(([1-9][0-9]*)|(0[0-7]*)|(0[xX][0-9a-fA-F]+))(([uU][lL]?)|([uU]((ll)|(LL)))|([lL][uU]?)|(((ll)|(LL))[uU]?))?" [token]
  syntax Char ::= r"[LuU]?'(([^'\\n\\\\])|(\\\\['\\\"?\\\\abfnrtv])|(\\\\[0-7]{3})|(\\\\x[0-9a-fA-F]+)|(\\\\u[0-9a-fA-F]{4})|(\\\\U[0-9a-fA-F]{8}))+'" [token]

endmodule

module C18-COMMON
  imports C-LEXICAL-SORTS

  // \section(A.2.1)

  syntax Exp ::= Identifier
               | Constant
               | StringLiteral
               | "(" Exp ")" [bracket]
               | "_Generic" "(" Exp "," GenericAssocs ")"
               > Exp "[" Exp "]"
               | Exp "(" Exps ")"
               | Exp "(" ")"
               | Exp "." Identifier
               | Exp "->" Identifier
               | Exp "++"
               | Exp "--"
               | "(" TypeName ")" "{" Inits "}"
               | "(" TypeName ")" "{" Inits "," "}"
               > "++" Exp
               | "--" Exp
               | "&" Exp
               | "*" Exp
               | "+" Exp
               | "-" Exp
               | "~" Exp
               | "!" Exp
               | "sizeof" Exp
               | "sizeof" "(" TypeName ")"
               | "_Alignof" "(" TypeName ")"
               > "(" TypeName ")" Exp
               > left:
                 Exp "*" Exp
               | Exp "/" Exp
               | Exp "%" Exp
               > left:
                 Exp "+" Exp
               | Exp "-" Exp
               > left:
                 Exp "<<" Exp
               | Exp ">>" Exp
               > left:
                 Exp "<" Exp
               | Exp ">" Exp
               | Exp "<=" Exp
               | Exp ">=" Exp
               > left:
                 Exp "==" Exp
               | Exp "==" Exp
               > left:
                 Exp "&" Exp
               > left:
                 Exp "^" Exp
               > left:
                 Exp "|" Exp
               > left:
                 Exp "&&" Exp
               > left:
                 Exp "||" Exp
               > right:
                 Exp "?" Exp ":" Exp
               > right:
                 Exp "=" Exp [assign]
               | Exp "*=" Exp [assign]
               | Exp "/=" Exp [assign]
               | Exp "%=" Exp [assign]
               | Exp "+=" Exp [assign]
               | Exp "-=" Exp [assign]
               | Exp "<<=" Exp [assign]
               | Exp ">>=" Exp [assign]
               | Exp "&=" Exp [assign]
               | Exp "^=" Exp [assign]
               | Exp "|=" Exp [assign]
               > left:
                 Exp "," Exp [comma]
  syntax priorities assignExp > comma
  syntax priorities constantExp > assign

  syntax GenericAssocs ::= NeList{GenericAssoc,","}

  syntax GenericAssoc ::= TypeName ":" Exp  [assignExp]
                              | "default" ":" Exp [assignExp]

  syntax Exps ::= Exp [klabel(arg), assignExp]
                | Exps "," Exp [assignExp]

  // \section(A.2.2)

  syntax Decl ::= DeclSpecifiers InitDecls ";"
                | DeclSpecifiers ";"
                | StaticAssertDecl

  syntax DeclSpecifiers ::= NeList{DeclSpecifier,""}

  syntax DeclSpecifier ::= StorageClassSpecifier
                         | TypeSpecifier
                         | TypeQualifier
                         | FunctionSpecifier
                         | AlignmentSpecifier

  syntax InitDecls ::= NeList{InitDecl,","}

  syntax InitDecl ::= Declarator
                    | Declarator "=" Init

  syntax StorageClassSpecifier ::= "typedef"
                                 | "extern"
                                 | "static"
                                 | "_Thread_local"
                                 | "auto"
                                 | "register"

  syntax TypeSpecifier ::= "void"
                         | "char"
                         | "short"
                         | "int"
                         | "long"
                         | "float"
                         | "double"
                         | "signed"
                         | "unsigned"
                         | "_Bool"
                         | "_Complex"
                         | AtomicTypeSpecifier
                         | "struct" Identifier "{" StructDecls "}"
                         | "struct" "{" StructDecls "}"
                         | "struct" Identifier
                         | "union" Identifier "{" StructDecls "}"
                         | "union" "{" StructDecls "}"
                         | "union" Identifier
                         | "enum" Identifier "{" Enumerators "}"
                         | "enum" "{" Enumerators "}"
                         | "enum" Identifier "{" Enumerators "," "}"
                         | "enum" "{" Enumerators "," "}"
                         | "enum" Identifier
                         | Identifier

  syntax AtomicTypeSpecifier ::= "_Atomic" "(" TypeName ")"

  syntax StructDecls ::= NeList{StructDecl,""}

  syntax StructDecl ::= SpecifierQuals StructDeclarators ";"
                      | SpecifierQuals ";"
                      | StaticAssertDecl

  syntax SpecifierQuals ::= NeList{SpecifierQual,""}

  syntax SpecifierQual ::= TypeSpecifier
                         | TypeQualifier

  syntax StructDeclarators ::= NeList{StructDeclarator,","}

  syntax StructDeclarator ::= Declarator
                            | Declarator ":" Exp [constantExp]
                            | ":" Exp [constantExp]

  syntax Enumerators ::= NeList{Enumerator,","}

  syntax Enumerator ::= Identifier
                      | Identifier "=" Exp [constantExp]

  syntax TypeQualifier ::= "const" | "restrict" | "volatile" | "_Atomic"
  syntax FunctionSpecifier ::= "inline" | "_Noreturn"
  syntax AlignmentSpecifier ::= "_Alignas" "(" TypeName ")"
                              | "_Alignas" "(" Exp ")"

  syntax Declarator ::= Pointer DirectDeclarator
                      | DirectDeclarator

  syntax DirectDeclarator ::= Identifier
                            | "(" Declarator ")"
                            | DirectDeclarator "[" TypeQualifiers Exp "]"
                            | DirectDeclarator "[" TypeQualifiers "]"
                            | DirectDeclarator "[" Exp "]"
                            | DirectDeclarator "[" "]"
                            | DirectDeclarator "[" "static" TypeQualifiers Exp "]"
                            | DirectDeclarator "[" "static" Exp "]"
                            | DirectDeclarator "[" TypeQualifiers "static" Exp "]"
                            | DirectDeclarator "[" TypeQualifiers "*" "]"
                            | DirectDeclarator "[" "*" "]"
                            | DirectDeclarator "(" ParamTypeList ")"
                            | DirectDeclarator "(" Identifiers ")"
                            | DirectDeclarator "(" ")"

  syntax FunctionDeclarator ::= Pointer FunctionDirectDeclarator
                              | FunctionDirectDeclarator

  syntax FunctionDirectDeclarator ::= "(" FunctionDeclarator ")"
                                    | DirectDeclarator "(" ParamTypeList ")"
                                    | DirectDeclarator "(" Identifiers ")"
                                    | DirectDeclarator "(" ")"

  syntax Pointer ::= "*"
                   | "*" TypeQualifiers
                   | "*" Pointer
                   | "*" TypeQualifiers Pointer

  syntax TypeQualifiers ::= NeList{TypeQualifier,""}

  syntax ParamTypeList ::= Params
                         | Params "," "..."

  syntax Params ::= NeList{ParamDecl,","}

  syntax ParamDecl ::= DeclSpecifiers Declarator
                     | DeclSpecifiers
                     | DeclSpecifiers AbstractDeclarator

  syntax Identifiers ::= NeList{Identifier,","}

  syntax TypeName ::= SpecifierQuals
                    | SpecifierQuals AbstractDeclarator

  syntax AbstractDeclarator ::= Pointer
                              | DirectAbstractDeclarator
                              | Pointer DirectAbstractDeclarator

  syntax DirectAbstractDeclarator ::= "(" AbstractDeclarator ")"
                                    | "[" "]"
                                    | "[" TypeQualifiers "]"
                                    | "[" TypeQualifiers Exp "]"
                                    | DirectAbstractDeclarator "[" Exp "]"
                                    | "[" "static" Exp "]"
                                    | "[" "static" TypeQualifiers Exp "]"
                                    | DirectAbstractDeclarator "[" "static" Exp "]"
                                    | DirectAbstractDeclarator "[" "static" TypeQualifiers Exp "]"
                                    | DirectAbstractDeclarator "[" TypeQualifiers "static" Exp "]"
                                    | "[" TypeQualifiers "static" Exp "]"
                                    | "[" "*" "]"
                                    | DirectAbstractDeclarator "[" "*" "]"
                                    | "(" ")"
                                    | "(" ParamTypeList ")"
                                    | DirectAbstractDeclarator "(" ")"
                                    | DirectAbstractDeclarator "(" ParamTypeList ")"

  syntax Init ::= Exp [klabel(initExp), assignExp]
                | "{" Inits "}"
                | "{" Inits "," "}"

  syntax Inits ::= NeList{InitDesignation,","}

  syntax InitDesignation ::= Init | Designators "=" Init

  syntax Designators ::= NeList{Designator,""}

  syntax Designator ::= "[" Exp "]"
                      | "." Identifier

  syntax StaticAssertDecl ::= "_Static_assert" "(" Exp "," StringLiteral ")" ";"

  // \section(A.2.3)

  syntax Stmt ::= Identifier ":" Stmt
                | "case" Exp ":" Stmt
                | "default" ":" Stmt
                | CompoundStmt
                | ";"
                | Exp ";"
                | "if" "(" Exp ")" Stmt
                | "if" "(" Exp ")" Stmt "else" Stmt [avoid]
                | "switch" "(" Exp ")" Stmt
                | "while" "(" Exp ")" Stmt
                | "do" Stmt "while" "(" Exp ")" ";"
                | "for" "("     ";"     ";"     ")" Stmt
                | "for" "("     ";" Exp ";"     ")" Stmt
                | "for" "("     ";" Exp ";" Exp ")" Stmt
                | "for" "("     ";"     ";" Exp ")" Stmt
                | "for" "(" Exp ";"     ";"     ")" Stmt
                | "for" "(" Exp ";" Exp ";"     ")" Stmt
                | "for" "(" Exp ";" Exp ";" Exp ")" Stmt
                | "for" "(" Exp ";"     ";" Exp ")" Stmt
                | "for" "(" Decl     ";"     ")" Stmt
                | "for" "(" Decl Exp ";"     ")" Stmt
                | "for" "(" Decl Exp ";" Exp ")" Stmt
                | "for" "(" Decl     ";" Exp ")" Stmt
                | "goto" Identifier
                | "continue" ";"
                | "break" ";"
                | "return" ";"
                | "return" Exp ";"


  syntax CompoundStmt ::= "{" BlockItems "}" [format(%1%i%n%2%d%n%3)]
                        | "{" "}" [format(%1%2)]

  syntax BlockItems ::= NeList{BlockItem,""} [format(%1%n%3)]
  syntax BlockItem ::= Decl | Stmt

  // \section(A.2.4)

  syntax TranslationUnit ::= NeList{ExtDecl,""} [format(%1%n%3)]

  syntax ExtDecl ::= FunDefn | Decl

  syntax FunDefn ::= DeclSpecifiers FunctionDeclarator Decls CompoundStmt [format(%1 %2%n%i%3%d %4)]
                   | DeclSpecifiers FunctionDeclarator CompoundStmt [format(%1 %2 %3)]

  syntax Decls ::= NeList{Decl,""}

endmodule

module C18-BASE
  imports C18-COMMON
  imports ID
  imports STRING
  imports INT
  imports FLOAT

  syntax Identifier ::= Id
  syntax Constant ::= Int | Float | Id
  syntax StringLiteral ::= String
endmodule

module C18-SYNTAX
  imports C18-COMMON
  imports C-LEXICAL
endmodule
