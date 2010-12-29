grammar annot;


options {
  //k = 2;
  //backtrack = true;
  //memoize = true;
  output = AST;
  ASTLabelType=CommonTree;
}


tokens {
  BEGIN_ANNOT = '/*@';
  END_ANNOT = '*/';

  PRE = 'pre';
  POST = 'post';
  ASSUME = 'assume';
  ASSERT = 'assert';
  INVARIANT = 'invariant';
  SKIP = 'skip';
  VERIFY = 'verify';

  DOT = '.';
  COLON = ':';
  COMMA = ',';
  LPAREN = '(';
  RPAREN = ')'; 
  ANY = '_';

  DISJ = '\\/';
  CONJ = '/\\';
  NEG = '~';

  EQ = '=';
  LT = '<';
  LEQ = '<=';
  GT = '>';
  GEQ = '>=';

  UNION = 'U';
  APPEND = '@';
  ADD = '+';
  SUB = '-';
  MUL = '*';
  DIV = '/';
  REM = '%';
  SIGN_POS;
  SIGN_NEG;

  MATH_OBJ_LIST;
  MATH_OBJ_LIST_UNIT = '.List{MathObj++}';

  SEQ;
  MSET;

  K_UNIT = '.K';
  K_ARROW = '~>';

  K_LIST;
  K_LIST_UNIT = '.List{K}';
  K_LIST_COMMA = ',,';

  MAP;
  MAP_UNIT = '.Map';
  MAP_ITEM = 'MapItem';
  MAPSTO = '|->';
  POINTSTO;
  HEAP_PATTERN;

  BAG;
  BAG_UNIT = '.Bag';
  BAG_ITEM = 'BagItem';

  CELL;

  LIST;
  LIST_UNIT = '.List';
  LIST_ITEM = 'ListItem';

  TERM_LIST;

  FIELD;

  IDENTIFIER;
  LETTER;
  DIGIT;
  FORMULA_TRUE = 'true';
  FORMULA_FALSE = 'false';
  DECIMAL_LITERAL;
  OCTAL_LITERAL;
  HEX_LITERAL;
  HEX_DIGIT;

  WHITESPACE;
}

annot
  : BEGIN_ANNOT!
    ( pattern_directive^ pattern
    | function_directive
    )
    END_ANNOT!
  ;

pattern_directive
  : PRE
  | POST
  | ASSUME
  | ASSERT
  | INVARIANT
  ;

function_directive
  : SKIP
  | VERIFY
  ;


pattern
  : disjunctive_pattern
  ;

disjunctive_pattern
  : primary_pattern (DISJ^ primary_pattern)*
  ;

primary_pattern
options { backtrack = true; }
  : configuration
    ( -> ^(CONJ configuration FORMULA_TRUE)
    | CONJ formula -> ^(CONJ configuration formula)
    )
  | LPAREN pattern RPAREN
    ( -> pattern
    | CONJ formula -> ^(CONJ pattern formula)
    )
  ;


configuration
  : bag
  ;

//term_list
//  : term (COMMA term)* -> ^(TERM_LIST term+)
//  ;

term
options { backtrack = true; }
  : map
  | bag
  | k
  ;


/*
 * Grammar rules for map parsing
 */
map
  //: map_item+ -> ^(MAP map_item+)
  : map_item (COMMA map_item)* -> ^(MAP map_item+)
  | map_unit -> MAP
  ;


map_unit
  : DOT
  | MAP_UNIT
  ;

map_item
options { backtrack = true; }
  : points_to
  | maps_to
  | heap_pattern
  | IDENTIFIER
  | map_constructor
  //| infix_map
  | LPAREN! map RPAREN!
  ;

map_constructor
  : MAP_ITEM^ LPAREN! k RPAREN!
  ;

maps_to
  : k_list MAPSTO^ k_list
  ;

points_to
  : o1=mathematical_object MAPSTO o2=mathematical_object COLON mem_type
    -> ^(POINTSTO $o1 $o2 mem_type)
  ;

mem_type
  : IDENTIFIER
    ( -> IDENTIFIER
    | DOT mem_type -> ^(FIELD IDENTIFIER mem_type)
    )
  ;

heap_pattern
  : heap_pattern_name
    LPAREN l1=mathematical_object_list RPAREN 
    LPAREN l2=mathematical_object_list RPAREN
    -> ^(HEAP_PATTERN heap_pattern_name $l1 $l2)
  ;

heap_pattern_name
  : IDENTIFIER
  ;

//infix_map
//  : IDENTIFIER LPAREN term_list RPAREN
//  ;


/*
 * Grammar rules for bag parsing
 */
bag
  : bag_item+ -> ^(BAG bag_item+)
  | bag_unit -> BAG
  ;

bag_unit
  : DOT
  | BAG_UNIT
  ;

bag_item
  : IDENTIFIER
  | bag_constructor
  | cell
  // | infix_bag
  | LPAREN! bag RPAREN!
  ;

bag_constructor
  : BAG_ITEM^ LPAREN! k RPAREN!
  ;

//infix_bag
//  : IDENTIFIER LPAREN term_list RPAREN
//  ;


/*
 * Grammar rules for cell parsing (for now only closed cells)
 */
cell
  : '<' ml1=map_cell_label '>' map '</' ml2=map_cell_label '>'
    { $ml2.text.equals($ml1.text)}?
    -> ^(CELL $ml1 map $ml2)
  | '<' bl1=bag_cell_label '>' bag '</' bl2=bag_cell_label '>'
    { $bl2.text.equals($bl1.text)}?
    -> ^(CELL $bl1 bag $bl2)
  ;

map_cell_label
  : 'env'
  | 'heap'
  ;

bag_cell_label
  : 'config'
  ;


/*
 * Grammar rules for k parsing
 */
k_list
  : k (K_LIST_COMMA k)* -> ^(K_LIST k+)
  | K_LIST_UNIT -> K_LIST
  ;

k
  : formula (K_ARROW^ formula)*
  ;


/*
 * Grammar rules for formula parsing
 */
formula
  : disjunction_formula
  ;

disjunction_formula
//options { backtrack = true; }
  //: conjunction_formula (DISJ^ conjunction_formula)*
  : conjunction_formula
    ((DISJ conjunction_formula)=> DISJ^ conjunction_formula)*
  ;

conjunction_formula
  : negation_formula (CONJ^ negation_formula)*
  ;

negation_formula
  : (NEG^)* atomic_formula
  ;

atomic_formula
  : mathematical_object ((EQ | LT | LEQ | GT | GEQ)^ mathematical_object)?
  ;


/*
 * Grammar rules for mathematical objects (list, multiset, ...)
 */
mathematical_object_list
  : mathematical_object (COMMA mathematical_object)*
    -> ^(MATH_OBJ_LIST mathematical_object+)
  | MATH_OBJ_LIST_UNIT -> MATH_OBJ_LIST
  ;

mathematical_object
  : multiset_union_term
  ;

multiset_union_term
  : list_append_term (UNION^ list_append_term)*
  ;

list_append_term
  : integer_term (APPEND^ integer_term)*
  ;

/*
 * Grammar rules for integer terms parsing
 */
integer_term
  : additive_integer_term
  ;

additive_integer_term
  : multiplicative_integer_term ((ADD | SUB)^ multiplicative_integer_term)*
  ;

multiplicative_integer_term
  : unary_integer_term ((MUL | DIV | REM)^ unary_integer_term)*
  ;

unary_integer_term
  : (unary_operator^)* primary_term
  ;

unary_operator
  : ADD -> SIGN_POS
  | SUB -> SIGN_NEG
  ;

primary_term
  : IDENTIFIER
  | constant
  | constructor
  | infix_term
  | LPAREN! k RPAREN!
  ;

constant
  : DOT
  | K_UNIT
  | FORMULA_TRUE
  | FORMULA_FALSE
  | DECIMAL_LITERAL
  | OCTAL_LITERAL
  | HEX_LITERAL
  // | CHARACTER_LITERAL
  | STRING_LITERAL
  // | FLOATING_POINT_LITERAL
  ;

constructor
  : '[' mathematical_object_list ']' -> ^(SEQ mathematical_object_list)
  | '{' mathematical_object_list '}' -> ^(MSET mathematical_object_list)
  ;

infix_term
  //: IDENTIFIER^ LPAREN! term_list RPAREN!
  : IDENTIFIER^ LPAREN! mathematical_object_list RPAREN!
  ;


/*
 * Tokens
 */
IDENTIFIER : ('?' | '!' | LETTER) (LETTER | DIGIT)* ;
  
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

WHITESPACE : (' ' | '\r' | '\t' | '\u000C' | '\n') { skip(); } ;

