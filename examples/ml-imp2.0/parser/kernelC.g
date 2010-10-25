grammar kernelC;

options {
  output = AST;
  ASTLabelType = CommonTree;
  backtrack = true;
  memoize = true;
  k = 2;
}

tokens {
  LIST;
  SEQ;
  TRANS_UNIT;
  FUN_DEF;
  FUN_DECL;
  STRUCT_DECL;
  VAR_DECL;
  PARAM;
  STRUCT = 'struct';
  PTR;
  NOP;
  IF = 'if';
  ELSE = 'else';
  WHILE = 'while';
  RETURN = 'return';
  BLOCK;
  VOID_EXP;
  CAST;
  REF;
  DEREF;
  SIGN_POS;
  SIGN_NEG;
  INDEX;
  CALL;
  POST_INC;
  POST_DEC;
  ANNOT;
}

@lexer::header {
  import java.util.Set;
  import java.util.HashSet;
}

@lexer::members {
  HashSet<String> ids = new HashSet<String>();
  HashSet<String> annots = new HashSet<String>();
}



//
// Declarations
//
translation_unit
  : definition_declaration+ -> ^(TRANS_UNIT ^(SEQ definition_declaration+))
  ;

definition_declaration
options { k = 1; }
  : ( type IDENTIFIER '(' parameter_list ')' ANNOTATION ANNOTATION '{' )=>
    function_definition
  | declaration
  | ANNOTATION!
  ;

function_definition
  : type IDENTIFIER '(' parameter_list ')'
    ANNOTATION ANNOTATION
    compound_statement
    ->
    ^(FUN_DEF type IDENTIFIER parameter_list
      ANNOTATION ANNOTATION
      compound_statement
    )
  ;

declaration
  : struct_declaration
  | function_declaration
  | variable_declaration
  ;

function_declaration
  : type IDENTIFIER '(' parameter_list ')' ANNOTATION ANNOTATION ';'
    -> ^(FUN_DECL type IDENTIFIER parameter_list ANNOTATION ANNOTATION)
  ;

struct_declaration
  : STRUCT IDENTIFIER '{' struct_field_list '}' ';'
    -> ^(STRUCT_DECL IDENTIFIER struct_field_list)
  ;

struct_field_list
  : declaration+
    -> ^(LIST declaration+)
  ;

variable_declaration
  : type IDENTIFIER ';' -> ^(VAR_DECL type IDENTIFIER)
  ;

parameter_list
  : parameter (',' parameter)* 
    -> ^(LIST parameter+)
  | -> LIST
  ;

parameter
  : type IDENTIFIER -> ^(PARAM type IDENTIFIER)
  ;

type
  : ( 'void'
    | 'int'
    | STRUCT^ IDENTIFIER
    )
    (ptr^)*
  ;

ptr
  : '*' -> PTR
  ;


//
// Statements
//
statement_list
  : statement+
  | -> NOP
  ;

statement
  : expression ';' -> ^(';' expression)
  | ';' -> ^(';' VOID_EXP)
  | IF '(' expression ')' s1=statement
    (
    : ELSE s2=statement -> ^(IF expression $s1 $s2)
    | -> ^(IF expression statement NOP)
    )
  | WHILE '(' expression ')' statement -> ^(WHILE expression statement)
  | RETURN expression ';' -> ^(RETURN expression)
  | RETURN ';' -> ^(RETURN VOID_EXP)
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
  : '='
  | '*='
  | '/='
  | '%='
  | '+='
  | '-='
  | '<<='
  | '>>='
  | '&='
  | '^='
  | '|='
  ;

conditional_expression
  : logical_or_expression ('?'^ expression ':'! conditional_expression)?
  ;

logical_or_expression
  : logical_and_expression ('||'^ logical_and_expression)*
  ;

logical_and_expression
  : inclusive_or_expression ('&&'^ inclusive_or_expression)*
  ;

inclusive_or_expression
  : exclusive_or_expression ('|'^ exclusive_or_expression)*
  ;

exclusive_or_expression
  : and_expression ('^'^ and_expression)*
  ;

and_expression
  : equality_expression ('&'^ equality_expression)*
  ;
  
equality_expression
  : relational_expression (('=='|'!=')^ relational_expression)*
  ;

relational_expression
  : shift_expression (('<'|'>'|'<='|'>=')^ shift_expression)*
  ;

shift_expression
  : additive_expression (('<<'|'>>')^ additive_expression)*
  ;

additive_expression
  : multiplicative_expression (('+'|'-')^ multiplicative_expression)*
  ;

multiplicative_expression
  : cast_expression (('*'|'/'|'%')^ cast_expression)*
  ;

cast_expression
  : (cast_operator^ type ')'!)* unary_expression
  ;

cast_operator : '(' -> CAST ;

unary_expression
  : postfix_expression
  | '++'^ unary_expression
  | '--'^ unary_expression
  | unary_operator^ cast_expression
  | 'sizeof'^ unary_expression
  | 'sizeof'^ '('! type ')'!
  ;

unary_operator
  : '&' -> REF
  | '*' -> DEREF
  | '+' -> SIGN_POS
  | '-' -> SIGN_NEG
  | '~'
  | '!'
  ;

postfix_expression
  : primary_expression
    ( index_operator^ expression ']'!
    | call_operator^ argument_expression_list ')'!
    | '.'^ IDENTIFIER
    | '->'^ IDENTIFIER
    | post_inc_operator^
    | post_dec_operator^
    )*
  ;

index_operator : '[' -> INDEX ;

call_operator : '(' -> CALL;

post_inc_operator : '++' -> POST_INC;

post_dec_operator : '--' -> POST_DEC;

primary_expression
  : IDENTIFIER
  | constant
  | '('! expression ')'!
  ;

constant
  : arithmetic_constant
  //| CHARACTER_LITERAL
  //| STRING_LITERAL
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
IDENTIFIER : LETTER (LETTER | DIGIT)* { ids.add($text); } ;
  
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

HEX_LITERAL : '0' ('x' | 'X') HexDigit+ ;

fragment
HexDigit : '0'..'9' | 'a'..'f' | 'A'..'F' ;

ANNOTATION
  : ('/*@')=> '/*@' (options { greedy = false; } : .)* '*/'
    {
      int len = $text.length();
      annots.add($text.substring(3, len).substring(0, len - 5));
    }
  | ('//@')=> '//@' ~('\n' | '\r')* '\r'? '\n'
  | COMMENT
  | LINE_COMMENT
  ;

WHITESPACE : (' ' | '\r' | '\t' | '\u000C' | '\n') { skip(); } ;

fragment
COMMENT : '/*' (options { greedy = false; } : .)* '*/' { skip(); } ;

fragment
LINE_COMMENT : '//' ~('\n' | '\r')* '\r'? '\n' { skip(); } ;
