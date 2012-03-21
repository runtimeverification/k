interface K-MAP-EXTRAS
	including K-TECHNIQUE
	including #BOOL

	syntax K ::= Map "(" K ")" [prec(0)]

	syntax Map ::= Map "[" Map "]"     [prec(0)]
				 | Map "[" List{K} "/" List{K} "]" [prec(0)]
				 | Map "[" "undef" "/" List{K} "]"

	syntax List{K} ::= Map "(" List{K} ")" [prec(0)]

	syntax Set ::= "keys" Map  
endinterface

interface K-SET-EXTRAS
	including K-TECHNIQUE
	including #IF-THEN-ELSE

	syntax Set ::= "Set" List{K}
				 | Set "-Set" Set

	syntax #Bool ::= K "in" Set
				   | SetItem "in" Set	

endinterface

interface K-BAG-EXTRAS
	including K-TECHNIQUE
	including #IF-THEN-ELSE

	syntax Bag ::= "Bag" List{K}
				 | Bag "-Bag" Bag
	syntax #Bool ::= K "in" Bag
				   | BagItem "in" Bag
endinterface

interface K-LIST-EXTRAS
	including K-TECHNIQUE
	including #BOOL
	
	syntax List ::= "List" List{K}

	syntax #Int ::= "lengthList" List
endinterface

interface K-RESULT
	including K-TECHNIQUE

	syntax K ::= KResult
	
	//op .List{K} : -> List{KResult} [ditto metadata "latex=(renameTo \\ensuremath{\\dotCt{List\\{K\\}}})"] .

endinterface

interface K-WRAPPERS-LABELS
	including K-TECHNIQUE
	including #STRING

	syntax KLabel ::= "wklabel" KLabel
					| "wcelllabel" CellLabel
					| "kList" #String
					| "wbag" Bag
					| "wset" Set
					| "wlist" List
					| "wmap" Map
					| "wrap-with"
	
endinterface
/*
interface K-WRAPPERS
	including K-TECHNIQUE
	
	syntax K ::= "wklabel" KLabel
			   | "wcelllabel" CellLabel
			   | "wklist" ListOfK
			   | "wset" Set
			   | "wbag" Bag
			   | "wlist" List
			   | "wmap" Map
endinterface
*/

interface K
  including K-TECHNIQUE
  including K-WRAPPERS
  including K-BUILTINS
  including K-RESULT             // to express results syntactically
  including K-RULES              // to write k rules with in-place rewriting
  including K-CONFIG             // to specify the global configuration term
  including K-EVAL
  including K-POLYMORPHIC-VARIABLES // defines the ? polmorfic constant
  including K-OPEN-CELLS            // defines open cells like <_>..._...</_> 
  including K-CONTEXTS  
  including K-DESTRUCTORS           // defines getKLabel and getList{K} for K
  including K-EXTRAS                // defines a KLabel substitution 
  including K-LISTK-EXTRAS  
  including K-LIST-EXTRAS  
  including K-MAP-EXTRAS            // operations on Maps
  including K-BAG-EXTRAS            // operations on Bags
  including K-SET-EXTRAS            // operations on Sets
  including K-LATEX  
endinterface
