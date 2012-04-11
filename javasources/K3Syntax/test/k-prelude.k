require "builtins/builtins.k"

interface K-MAP-EXTRAS
	imports K-TECHNIQUE
	imports #BOOL

	syntax K ::= Map "(" K ")" [prec(0)]

	syntax Map ::= Map "[" Map "]"     [prec(0)]
				 | Map "[" List{K} "/" List{K} "]" [prec(0)]
				 | Map "[" "undef" "/" List{K} "]"

	syntax List{K} ::= Map "(" List{K} ")" [prec(0)]

	syntax Set ::= "keys" Map  
endinterface

interface K-SET-EXTRAS
	imports K-TECHNIQUE
	imports #IF-THEN-ELSE

	syntax Set ::= "Set" List{K}
				 | Set "-Set" Set

	syntax #Bool ::= K "in" Set
				   | SetItem "in" Set	

endinterface

interface K-BAG-EXTRAS
	imports K-TECHNIQUE
	imports #IF-THEN-ELSE

	syntax Bag ::= "Bag" List{K}
				 | Bag "-Bag" Bag
	syntax #Bool ::= K "in" Bag
				   | BagItem "in" Bag
endinterface

interface K-LIST-EXTRAS
	imports K-TECHNIQUE
	imports #BOOL

	syntax List ::= "List" List{K}

	syntax #Int ::= "lengthList" List
endinterface

interface K-RESULT
	imports K-TECHNIQUE

	syntax K ::= KResult

	//op .List{K} : -> List{KResult} [ditto metadata "latex=(renameTo \\ensuremath{\\dotCt{List\\{K\\}}})"] .

endinterface

interface K-WRAPPERS-LABELS
	imports K-TECHNIQUE
	imports #STRING

	syntax KLabel ::= "wklabel" KLabel
					| "wcelllabel" CellLabel
					| "kList" #String
					| "wbag" Bag
					| "wset" Set
					| "wlist" List
					| "wmap" Map
					| "wrap-with"

endinterface

interface K-DESTRUCTORS
	syntax KLabel ::= "getKLabel" K

endinterface


/*
interface K-WRAPPERS
	imports K-TECHNIQUE

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
  imports K-TECHNIQUE
  imports K-WRAPPERS
  imports K-BUILTINS
  imports K-RESULT             // to express results syntactically
  imports K-RULES              // to write k rules with in-place rewriting
  imports K-CONFIG             // to specify the global configuration term
  imports K-EVAL
  imports K-POLYMORPHIC-VARIABLES // defines the ? polmorfic constant
  imports K-OPEN-CELLS            // defines open cells like <_>..._...</_> 
  imports K-CONTEXTS  
  imports K-DESTRUCTORS           // defines getKLabel and getList{K} for K
  imports K-EXTRAS                // defines a KLabel substitution 
  imports K-LISTK-EXTRAS  
  imports K-LIST-EXTRAS  
  imports K-MAP-EXTRAS            // operations on Maps
  imports K-BAG-EXTRAS            // operations on Bags
  imports K-SET-EXTRAS            // operations on Sets
  imports K-LATEX  
endinterface
