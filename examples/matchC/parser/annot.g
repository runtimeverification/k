grammar annot;


options {
  tokenVocab = k;
  //k = 2;
  output = AST;
  ASTLabelType=CommonTree;
}


tokens {
  BEGIN_ANNOT = '/*@';
  END_ANNOT = '*/';
  LINE_ANNOT = '//@';

  PRE = 'pre';
  POST = 'post';
  ASSUME = 'assume';
  ASSERT = 'assert';
  INVARIANT = 'invariant';
  SKIP = 'skip';
  VERIFY = 'verify';
  BREAKPOINT = 'breakpoint';
  VAR;

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
  EPSILON = 'epsilon';

  MATH_OBJ_LIST;
  MATH_OBJ_LIST_UNIT = '.List{MathObj++}';

  SEQ;
  MSET;

  // MAP;
  MAP_UNIT = '.Map';
  MAP_ITEM = 'MapItem';
  MAPSTO = '|->';
  POINTSTO;
  HEAP_PATTERN;

  // BAG;
  BAG_UNIT = '.Bag';
  BAG_ITEM = 'BagItem';

  CONFIG;
  CELL;
  LABEL;

  // LIST;
  LIST_UNIT = '.List';
  LIST_ITEM = 'ListItem';
  STREAM;

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

  ID;
}


@lexer::members {
  boolean isVar = false;
}


annot
  : (BEGIN_ANNOT | LINE_ANNOT)
    ( pattern_directive pattern -> ^(pattern_directive ^(LIST pattern))
    | directive -> directive
    )
    END_ANNOT?
  ;

pattern_directive
  : PRE { Table.genVarString(""); }
  | POST
  | ASSUME { Table.genVarString("!"); }
  | ASSERT { Table.genVarString("!"); }
  | INVARIANT { Table.genVarString("!"); }
  ;

directive
  : SKIP
  | VERIFY
  | BREAKPOINT
  | VAR
    // ids+=IDENTIFIER (COMMA ids+=IDENTIFIER)* COLON sort=IDENTIFIER
    ids+=IDENTIFIER (COMMA ids+=IDENTIFIER)* COLON sort
    {
      for (Object id : $ids) {
        Table.varRootToSort.put(((CommonToken) id).getText(), $sort.text);
      }
    }
    -> VAR["(.).K"]
  ;

sort
  : IDENTIFIER
  | LIST_ITEM
  | BAG_ITEM
  | MAP_ITEM 
  ;

pattern
  : disjunctive_pattern
  ;

disjunctive_pattern
  : primary_pattern (DISJ^ primary_pattern)*
  ;

primary_pattern
options { backtrack = true; }
  : LPAREN pattern RPAREN
    ( -> pattern
    | CONJ formula -> ^(CONJ pattern formula)
    )
  | configuration
    ( -> ^(CONJ["/\\"] configuration FORMULA_TRUE)
    | CONJ formula -> ^(CONJ configuration formula)
    )
  | formula
    -> ^(CONJ["/\\"] ^(CONFIG[""] BAG) formula)
  ;


configuration
  : bag -> ^(CONFIG[""] bag)
  ;

//term_list
//  : term (COMMA term)* -> ^(TERM_LIST term+)
//  ;

term
options { backtrack = true; }
  : map
  | bag
  | list
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
 * Grammar rules for list parsing
 */
list
  : mathematical_object -> ^(STREAM["stream"] mathematical_object)
  ;


/*
 * Grammar rules for cell parsing (for now only closed cells)
 */
cell
options { backtrack = true; }
  : map_cell
  | bag_cell
  | list_cell
  | k_cell
  ;

map_cell
  : '<' IDENTIFIER '>' { Table.labelToCell.containsKey($IDENTIFIER.text) }?
    { Table.labelToCell.get($IDENTIFIER.text).sort.equals(Table.Sort.MAP) }?
    map cell_end[$IDENTIFIER.text]
    -> ^(CELL LABEL[$IDENTIFIER.text] map LABEL[$IDENTIFIER.text])
  ;

bag_cell
  : '<' IDENTIFIER '>' { Table.labelToCell.containsKey($IDENTIFIER.text) }?
    { Table.labelToCell.get($IDENTIFIER.text).sort.equals(Table.Sort.BAG) }?
    bag cell_end[$IDENTIFIER.text]
    -> ^(CELL LABEL[$IDENTIFIER.text] bag LABEL[$IDENTIFIER.text])
  ;

list_cell
  : '<' IDENTIFIER '>' { Table.labelToCell.containsKey($IDENTIFIER.text) }?
    { Table.labelToCell.get($IDENTIFIER.text).sort.equals(Table.Sort.LIST) }?
    list cell_end[$IDENTIFIER.text]
    -> ^(CELL LABEL[$IDENTIFIER.text] list LABEL[$IDENTIFIER.text])
  ;

k_cell
  : '<' IDENTIFIER '>' { Table.labelToCell.containsKey($IDENTIFIER.text) }?
    { Table.labelToCell.get($IDENTIFIER.text).sort.equals(Table.Sort.K) }?
    k cell_end[$IDENTIFIER.text]
    -> ^(CELL LABEL[$IDENTIFIER.text] k LABEL[$IDENTIFIER.text])
  ;

cell_end[String label]
  : '</' IDENTIFIER '>' { $IDENTIFIER.text.equals($label) }?
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
  : DOT -> K_UNIT
  | K_UNIT
  | FORMULA_TRUE
  | FORMULA_FALSE
  | DECIMAL_LITERAL
  | OCTAL_LITERAL
  | HEX_LITERAL
  | EPSILON
  // | CHARACTER_LITERAL
  | STRING_LITERAL
  // | FLOATING_POINT_LITERAL
  ;

constructor
  : '[' mathematical_object_list ']' -> ^(SEQ mathematical_object_list)
  | '{' mathematical_object_list '}' -> ^(MSET mathematical_object_list)
  ;

primary_sequence
  : '[' mathematical_object_list ']' -> ^(SEQ mathematical_object_list)
  ;

primary_multiset
  : '{' mathematical_object_list '}' -> ^(MSET mathematical_object_list)
  ;

infix_term
  //: IDENTIFIER^ LPAREN! term_list RPAREN!
  : IDENTIFIER LPAREN mathematical_object (COMMA mathematical_object)* RPAREN
    -> ^(IDENTIFIER mathematical_object+)
  ;


/*
 * Tokens
 */
K_UNIT : '.K' ;
K_ARROW : '~>' ;

K_LIST_UNIT : '.List{K}' ;
K_LIST_COMMA : ',,' ;

VAR : 'var' { isVar = true; };

IDENTIFIER
  : ('?' | '!')? LETTER (LETTER | DIGIT)*
    { if (!isVar) Table.annotIdentifiers.add($text); }
  ;
  
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

