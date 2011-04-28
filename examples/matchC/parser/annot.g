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

  CONDITIONAL_RULE;
  SPECIFICATION;
  CONFIG;

  RULE;
  IF;
  REQUIRES;
  ENSURES;
  ASSUME;
  ASSERT;
  INVARIANT;
  SKIP;
  VERIFY;
  BREAKPOINT;
  VAR;

  DOT = '.';
  COLON = ':';
  COMMA = ',';
  LPAREN = '(';
  RPAREN = ')'; 

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

  REW = '=>';

  // MAP;
  MAP_UNIT = '.Map';
  MAP_ITEM = 'MapItem';
  MAPSTO = '|->';
  POINTSTO;
  HEAP_PATTERN;

  // BAG;
  BAG_UNIT = '.Bag';
  BAG_ITEM = 'BagItem';

  CELL;

  // LIST;
  LIST_UNIT = '.List';
  LIST_ITEM = 'ListItem';
  STREAM;

  TERM_LIST;

  FIELD;

  RETURN = 'return';
  DEFAULT_K = '$';

  IDENTIFIER;
  PRIME_IDENTIFIER;
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
  VALUE;

  LOGICAL_VARIABLE;
  PROGRAM_IDENTIFIER;
  PROGRAM_VARIABLE;
}


@members {
  static int annotType;
  static CommonTree retTree;
}

@lexer::members {
  boolean isVar = false;
}


annot_text
@init {
  annotType = -1;
  retTree = null;
}
  : BEGIN_ANNOT! annot END_ANNOT!
  | LINE_ANNOT! annot
  ;

annot
  : function_annot
  | line_annot
  | tool_annot
  ;

function_annot
  : rule
    ( condition
      -> ^(CONDITIONAL_RULE rule condition)
    | ( REQUIRES | ENSURES )=> requires ensures
      -> ^(SPECIFICATION rule requires ensures)
    )
    { Table.genVarString(""); annotType = RULE; }
  ;

rule
  : RULE configuration -> ^(WRAPPER["wbag_"] configuration)
  | -> ^(WRAPPER["wbag_"] ^(CONFIG[""] BAG))
  ;

condition
  : IF formula -> ^(WRAPPER["Formula_"] formula)
  | -> ^(WRAPPER["Formula_"] FORMULA_TRUE)
  ;

requires
  : REQUIRES formula -> ^(WRAPPER["Formula_"] formula)
  | -> ^(WRAPPER["Formula_"] FORMULA_TRUE)
  ;

ensures
  : ENSURES formula -> ^(WRAPPER["Formula_"] formula)
  | -> ^(WRAPPER["Formula_"] FORMULA_TRUE)
  ;

line_annot
  : line_keyword pattern { Table.genVarString("!"); }
    -> ^(line_keyword ^(WRAPPER["wlist_"] pattern))
  ;

line_keyword
  : ASSUME { annotType = ASSUME; }
  | ASSERT { annotType = ASSERT; }
  | INVARIANT { annotType = INVARIANT; }
  ;

tool_annot
  : SKIP
  | VERIFY
  | BREAKPOINT
  | VAR
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
options { backtrack = true; }
  : configuration
    ( -> ^(CONJ["/\\"] configuration FORMULA_TRUE)
    | CONJ formula -> ^(CONJ configuration formula)
    )
  | formula -> ^(CONJ["/\\"] ^(CONFIG[""] BAG) formula)
  ;

configuration
  : bag -> ^(CONFIG[""] bag)
  ;


//term_list
//  : term (COMMA term)* -> ^(TERM_LIST term+)
//  ;

//term
//options { backtrack = true; }
//  : map
//  | bag
//  | list
//  | k
//  ;


/*
 * Grammar rules for map parsing
 */
map
  : map_rewrite
  ;

map_rewrite
  : map_term ((REW map_term)=> REW^ map_term)?
  ;

map_term
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
  | logical_variable
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
  : program_identifier
    ( -> program_identifier
    | DOT mem_type -> ^(FIELD program_identifier mem_type)
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
  : bag_rewrite
  ;

bag_rewrite
  : bag_term (REW^ bag_term)?
  ;

bag_term
  : bag_item+ -> ^(BAG bag_item+)
  | bag_unit -> BAG
  ;

bag_unit
  : DOT
  | BAG_UNIT
  ;

bag_item
  : logical_variable
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
  : list_rewrite
  ;

list_rewrite
  : list_term (REW^ list_term)?
  ;

list_term
  : list_item+ -> ^(BAG list_item+)
  | list_unit -> LIST
  ;

list_unit
  : DOT
  | LIST_UNIT
  ;

list_item
  : logical_variable
  | list_constructor
  // | infix_list
  | LPAREN! list RPAREN!
  ;

list_constructor
  : LIST_ITEM^ LPAREN! k RPAREN!
  ;

stream_list
  : k -> ^(STREAM["stream"] k)
  ;


/*
 * Grammar rules for cell parsing (for now only closed cells)
 */
cell
scope {
  String cellLabel;
  int cellOpen;

}
@init {
  $cell::cellOpen = Table.Cell.NONE;
}
  : open_cell_tag cell_content close_cell_tag
    -> ^(CELL[Integer.toString($cell::cellOpen)]
         open_cell_tag cell_content close_cell_tag
       )
  ;

open_cell_tag
  : '<'! IDENTIFIER ('>'! | '_>'! { $cell::cellOpen |= Table.Cell.LEFT; })
    { $cell::cellLabel = $IDENTIFIER.text; }
  ;

cell_content
  : { Table.Sort.MAP.equals(Table.labelToCell.get($cell::cellLabel).sort) }?=>
    map
  | { Table.Sort.BAG.equals(Table.labelToCell.get($cell::cellLabel).sort) }?=>
    bag
  | { Table.Sort.LIST.equals(Table.labelToCell.get($cell::cellLabel).sort)
      && !"in".equals($cell::cellLabel) && !"out".equals($cell::cellLabel) }?=>
    list
  | { "in".equals($cell::cellLabel) || "out".equals($cell::cellLabel) }?=>
    stream_list
  | { Table.Sort.K.equals(Table.labelToCell.get($cell::cellLabel).sort) }?=>
    k
  ;

close_cell_tag
  : ('</'! | '<_/'! { $cell::cellOpen |= Table.Cell.RIGHT; })  IDENTIFIER '>'!
    { $cell::cellLabel.equals($IDENTIFIER.text) }?
  ;


/*
 * Grammar rules for k parsing
 */
k_list
  : k (K_LIST_COMMA k)* -> ^(K_LIST k+)
  | K_LIST_UNIT -> K_LIST
  ;

k
  : k_rewrite
  ;

k_rewrite
  : k_term ((REW k_term)=> REW^ k_term)?
  ;

k_term
  : k_item (K_ARROW^ k_item)*
  ;

k_item
  : formula
  | DEFAULT_K -> K_UNIT[".K"]
  | RETURN mathematical_object ';' { retTree = $mathematical_object.tree; }
    -> K_UNIT[".K"]
  | RETURN ';' -> K_UNIT[".K"]
  ;


/*
 * Grammar rules for formula parsing
 */
formula
  : disjunction_formula
  ;

disjunction_formula
  : conjunction_formula (DISJ^ conjunction_formula)*
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
  : primary_identifier
  | PRIME_IDENTIFIER
  | constructor
  | infix_term
  | constant
  | LPAREN! k RPAREN!
  ;

constructor
  : '[' mathematical_object_list ']' -> ^(SEQ mathematical_object_list)
  | '{' mathematical_object_list '}' -> ^(MSET mathematical_object_list)
  ;

infix_term
  //: IDENTIFIER^ LPAREN! term_list RPAREN!
  : IDENTIFIER LPAREN mathematical_object (COMMA mathematical_object)* RPAREN
    -> ^(IDENTIFIER mathematical_object+)
  ;

primary_identifier
  : logical_variable
  | program_identifier
  | program_variable
  ;

constant
  //: DOT -> K_UNIT
  : K_UNIT
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


logical_variable
  : { !Table.kernelCIdentifiers.contains(input.LT(1).getText()) }?
    IDENTIFIER -> LOGICAL_VARIABLE[$IDENTIFIER]
  ;

program_identifier
  : { Table.kernelCIdentifiers.contains(input.LT(1).getText())
      && !Table.kernelCVariables.contains(input.LT(1).getText()) }?
    IDENTIFIER -> PROGRAM_IDENTIFIER[$IDENTIFIER]
  ;

program_variable
  : { Table.kernelCVariables.contains(input.LT(1).getText()) }?
    IDENTIFIER -> PROGRAM_VARIABLE[$IDENTIFIER]
  ;

/*
 * Tokens
 */
K_UNIT : '.K' ;
K_ARROW : '~>' ;

K_LIST_UNIT : '.List{K}' ;
K_LIST_COMMA : ',,' ;


RULE : 'rule' ;
IF : 'if' ;
REQUIRES : 'requires' | 'req' ;
ENSURES : 'ensures' | 'ens' ;
ASSUME : 'assume' ;
ASSERT : 'assert' ;
INVARIANT : 'invariant' | 'inv' ;
SKIP : 'skip' ;
VERIFY : 'verify' ;
BREAKPOINT : 'breakpoint' ;
VAR : 'var' { isVar = true; };

PRIME_IDENTIFIER
  : LETTER (LETTER | DIGIT)* '\''
    { if (!isVar) Table.annotIdentifiers.add($text); }
  ;
 
IDENTIFIER
  : ('?' | '!')? LETTER (LETTER | DIGIT)*
    {
      if (!isVar)
      {
        Table.annotIdentifiers.add($text);
        if (Table.kernelCVariables.contains($text))
          Table.annotLocalVariables.add($text);
      }
    }
  ;
  
fragment
LETTER
  :  '$'
  |  'A'..'Z'
  |  'a'..'z'
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

