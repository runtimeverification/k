grammar kernelC;


options {
  tokenVocab = k;
  output = AST;
  ASTLabelType = CommonTree;
  backtrack = true;
  memoize = true;
  k = 2;
}


tokens {
  SEQ;
  LIST;
  TRANS_UNIT;
  INT_TYPE = 'int';
  STRING_TYPE;
  VOID_TYPE = 'void';
  FUN_DEF;
  ANNOT_FUN_DEF;
  FUN_DECL;
  ANNOT_FUN_DECL;
  STRUCT_DECL;
  VAR_DECL;
  PARAM;
  STRUCT = 'struct';
  PTR;
  NOP;
  SEP = ';';
  IF = 'if';
  ELSE = 'else';
  WHILE = 'while';
  RETURN = 'return';
  BLOCK;
  VOID_EXP;
  ANNOT;

  ASSIGN = '=';
  OR_ASSIGN = '|=';
  XOR_ASSIGN = '^=';
  AND_ASSIGN = '&=';
  SHL_ASSIGN = '<<=';
  SHR_ASSIGN = '>>=';
  ADD_ASSIGN = '+=';
  SUB_ASSIGN = '-=';
  MUL_ASSIGN = '*=';
  DIV_ASSIGN = '/=';
  REM_ASSIGN = '%=';
  COND;
  LOR = '||';
  LAND = '&&';
  OR = '|';
  XOR = '^';
  AND = '&';
  EQ = '==';
  NEQ = '!=';
  LT = '<';
  GT = '>';
  LEQ = '<=';
  GEQ = '>=';
  SHL = '<<';
  SHR = '>>';
  ADD = '+';
  SUB = '-';
  MUL = '*';
  DIV = '/';
  REM = '%';
  INC = '++';
  DEC = '--';
  PRE_INC;
  PRE_DEC;
  SIZEOF = 'sizeof';
  CAST;
  REF;
  DEREF;
  SIGN_POS;
  SIGN_NEG;
  NOT = '~';
  NEG = '!';
  DOT = '.';
  ARROW = '->';
  INDEX;
  CALL;
  POST_INC;
  POST_DEC;

  TV;
  ID;
  UNIT_EXP;
}


@members {
  static boolean isVar = true;
}


//
// Declarations
//
translation_unit
  : definition_declaration+ -> ^(TRANS_UNIT ^(SEQ definition_declaration+))
  ;

definition_declaration
  : ( type IDENTIFIER '(' parameter_list ')' (ANNOTATION)? '{' )=>
    function_definition
  | declaration
  | ANNOTATION
  ;

function_definition
  : type IDENTIFIER
    '(' parameter_list ')'
    ( ANNOTATION compound_statement
      -> ^(ANNOT_FUN_DEF type IDENTIFIER parameter_list
           ANNOTATION compound_statement
         )
    | compound_statement
      -> ^(FUN_DEF type IDENTIFIER parameter_list compound_statement)
    )
  ;

declaration
  : struct_declaration
  | function_declaration
  | variable_declaration
  ;

function_declaration
  : type IDENTIFIER
    '(' parameter_list ')'
    ( ANNOTATION SEP
      -> ^(ANNOT_FUN_DECL type IDENTIFIER parameter_list ANNOTATION)
    | SEP -> ^(FUN_DECL type IDENTIFIER parameter_list)
    )
  ;

struct_declaration
  : STRUCT IDENTIFIER '{' struct_field_list '}' SEP
    -> ^(STRUCT_DECL IDENTIFIER struct_field_list)
  ;

struct_field_list
  : { isVar = false; } declaration+ { isVar = true; }
    -> ^(LIST declaration+)
  ;

variable_declaration
  : type IDENTIFIER SEP
    { if(isVar) Table.kernelCVariables.add($IDENTIFIER.text); }
    -> ^(VAR_DECL type IDENTIFIER)
  ;

parameter_list
  : parameter (',' parameter)* 
    -> ^(LIST parameter+)
  | -> LIST
  ;

parameter
  : type IDENTIFIER { Table.kernelCVariables.add($IDENTIFIER.text); }
    -> ^(PARAM type IDENTIFIER)
  ;

type
  : ( VOID_TYPE
    | INT_TYPE
    | STRUCT^ IDENTIFIER
    )
    (ptr^)*
  ;

ptr
  : MUL -> PTR
  ;


//
// Statements
//
statement_list
  : statement+
  | -> NOP
  ;

statement
  : expression SEP -> ^(SEP expression)
  | SEP -> NOP
  | IF '(' expression ')' s1=statement ELSE s2=statement
    -> ^(IF expression $s1 $s2)
  | IF '(' expression ')' statement -> ^(IF expression statement NOP)
  | WHILE '(' expression ')' statement -> ^(WHILE expression statement)
  | RETURN expression SEP -> ^(RETURN expression)
  | RETURN SEP -> ^(RETURN VOID_EXP)
  | compound_statement
  | ANNOTATION
  ;

compound_statement
  : '{' declaration* statement_list '}'
    -> ^(BLOCK ^(SEQ declaration* statement_list))
  ;

//
// Expressions
//
argument_expression_list
  : assignment_expression (',' assignment_expression)*
    -> ^(LIST assignment_expression+)
  | -> LIST
  ;

expression
  : assignment_expression //(',' assignment_expression)*
  ;

constant_expression
  : conditional_expression
  ;

assignment_expression
  : lvalue assignment_operator^ assignment_expression
  | conditional_expression
  ;
  
lvalue
  : unary_expression
  ;

assignment_operator
  : ASSIGN
  | OR_ASSIGN
  | XOR_ASSIGN
  | AND_ASSIGN
  | SHL_ASSIGN
  | SHR_ASSIGN
  | ADD_ASSIGN
  | SUB_ASSIGN
  | MUL_ASSIGN
  | DIV_ASSIGN
  | REM_ASSIGN
  ;

conditional_expression
  : logical_or_expression
    ( -> logical_or_expression
    | '?' expression ':' conditional_expression
      -> ^(COND logical_or_expression expression conditional_expression)
    )
  ;

logical_or_expression
  : logical_and_expression (LOR^ logical_and_expression)*
  ;

logical_and_expression
  : inclusive_or_expression (LAND^ inclusive_or_expression)*
  ;

inclusive_or_expression
  : exclusive_or_expression (OR^ exclusive_or_expression)*
  ;

exclusive_or_expression
  : and_expression (XOR^ and_expression)*
  ;

and_expression
  : equality_expression (AND^ equality_expression)*
  ;
  
equality_expression
  : relational_expression ((EQ | NEQ)^ relational_expression)*
  ;

relational_expression
  : shift_expression ((LT | GT | LEQ | GEQ)^ shift_expression)*
  ;

shift_expression
  : additive_expression ((SHL | SHR)^ additive_expression)*
  ;

additive_expression
  : multiplicative_expression ((ADD | SUB)^ multiplicative_expression)*
  ;

multiplicative_expression
  : cast_expression ((MUL | DIV | REM)^ cast_expression)*
  ;

cast_expression
  : (cast_operator^ type ')'!)* unary_expression
  ;

cast_operator : '(' -> CAST ;

unary_expression
  : postfix_expression
  | pre_inc_operator^ unary_expression
  | pre_dec_operator^ unary_expression
  | unary_operator^ cast_expression
  | SIZEOF^ unary_expression
  | SIZEOF^ '('! type ')'!
  ;

pre_inc_operator : INC -> PRE_INC;

pre_dec_operator : DEC -> PRE_DEC;

unary_operator
  : AND -> REF
  | MUL -> DEREF
  | ADD -> SIGN_POS
  | SUB -> SIGN_NEG
  | NOT
  | NEG
  ;

postfix_expression
  : primary_expression
    ( index_operator^ expression ']'!
    | call_operator^ argument_expression_list ')'!
    | DOT^ IDENTIFIER
    | ARROW^ IDENTIFIER
    | post_inc_operator^
    | post_dec_operator^
    )*
  ;

index_operator : '[' -> INDEX ;

call_operator : '(' -> CALL;

post_inc_operator : INC -> POST_INC;

post_dec_operator : DEC -> POST_DEC;

primary_expression
  : IDENTIFIER
  | constant
  | '('! expression ')'!
  ;

constant
  : arithmetic_constant
  //| CHARACTER_LITERAL
  | STRING_LITERAL
  //| FLOATING_POINT_LITERAL
  ;
  
arithmetic_constant
  : DECIMAL_LITERAL
  | OCTAL_LITERAL
  | HEX_LITERAL
  ;


//
// Tokens
//
IDENTIFIER : LETTER (LETTER | DIGIT)* { Table.kernelCIdentifiers.add($text); } ;
  
fragment
LETTER
  :  '$'
  |  'A'..'Z'
  |  'a'..'z'
  |  '_'
  ;

fragment
DIGIT :  '0'..'9' ;

DECIMAL_LITERAL : '0' | '1'..'9' ('0'..'9')* ;

OCTAL_LITERAL : '0' ('0'..'7')+ ;

HEX_LITERAL : '0' ('x' | 'X') HEX_DIGIT+ ;

fragment
HEX_DIGIT : '0'..'9' | 'a'..'f' | 'A'..'F' ;

STRING_LITERAL : '"' ( ESCAPE | ~('\\'|'"') )* '"' ;

fragment
ESCAPE : '\\' ('b'|'t'|'n'|'f'|'r'|'\"'|'\''|'\\') ;

ANNOTATION
  : ('/*@')=> '/*@' (options { greedy = false; } : .)* '*/'
  | ('//@')=> '//@' ~('\n' | '\r')* '\r'? '\n'
  | COMMENT
  | LINE_COMMENT
  ;

WHITESPACE : (' ' | '\r' | '\t' | '\u000C' | '\n') { skip(); } ;

fragment
COMMENT : '/*' (options { greedy = false; } : .)* '*/' { skip(); } ;

fragment
LINE_COMMENT : '//' ~('\n' | '\r')* '\r'? '\n' { skip(); } ;


// not a proper rule, but it works for now
PRE_PROC : '#include' ~('\n' | '\r')* '\r'? '\n' { skip(); } ;

