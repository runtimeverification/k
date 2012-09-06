require "builtins/builtins.k"

interface K-TECHNIQUE
	// all in SDF directly
endinterface

module K-LISTK-EXTRAS
  imports K-TECHNIQUE
  
  syntax Bool ::= K "inList{K}" List{K}
  syntax Bool ::= K "#inList{K}" List{K}
  rule K inList{K} L:List{K} => K #inList{K} L ==K true 
    [structural, anywhere]
  rule K #inList{K} (_,,K:K,,_) => true 
    [structural, anywhere]
endmodule

module K-MAP-EXTRAS
	imports K-TECHNIQUE
        imports K-SET-EXTRAS
	//imports BOOL

  syntax K ::= Map "(" K ")"
  rule (_ K1:K |-> K2:K)(K1) => K2 [structural, anywhere]

	syntax Map ::= Map "[" "undef" "/" List{K} "]"

  syntax Map ::= "Map" "(" List{K} "|->" List{K} ")" 
  rule Map((K1:K => .List{K}),,_ |-> (K2:K => .List{K}),,_) (. => K1 |-> K2)
  rule Map((K1:K => .List{K}),,_ |-> K2:K) (. => K1 |-> K2)
  rule Map(.List{K} |-> _) => .

  syntax Map ::= Map "[" List{K} "/" List{K} "]"
  rule (M:Map => M[K2/K1][K2'/K1'])[(K2:K,,K2':K => .List{K}),,_ 
                        /  (K1:K,,K1':K => .List{K}),,_]

  rule (M:Map K1:K |-> K2:K)[K2':K / K1] => M K1 |-> K2' 
    [structural, anywhere]
  rule M:Map[K2:K / K1:K] => M K1 |-> K2 
    when notBool(K1 in keys(M)) [structural, anywhere]
  
  syntax Map ::= Map "[" Map "]"   [cons(Map1UpdateMapWithMapSyn)]
  rule M:Map[M':Map K1 |-> K2] => M[K2/K1][M'] [structural]
  rule M:Map[.Map] => M [structural]

//  syntax List{K} ::= Map "(" List{K} ")"
//  rule Map:Map((K1:K,,K2:K,,Ks:List{K})) 
//    => Map(K1),,Map(K2),,Map(Ks) [structural]
//  rule Map:Map(.List{K}) => .List{K} [structural]

	syntax Set ::= "keys" Map  

  rule keys . => .
  rule (keys ((K:K |->_  => .) _)) (. => SetItem(K))

  syntax Bool ::= "$hasMapping" "(" Map "," K ")" [latex(latex=(renameTo \\$hasMapping\\mybracket{_,_})), maudeop("$hasMapping")]
  syntax Bool ::= "#hasMapping" "(" Map "," K ")" [latex(latex=(renameTo \\$hasMapping\\mybracket{_,_})), maudeop("#hasMapping")]
  rule $hasMapping(M:Map,K:K) => #hasMapping(M,K) ==K true [structural, anywhere]

  rule #hasMapping(M:Map K:K |-> _,K) => true [structural, anywhere]
endmodule

module K-SET-EXTRAS
	imports K-TECHNIQUE

	syntax Set ::= "Set" List{K}
				 | Set "-Set" Set

	syntax Bool ::= K "in" Set
			      | SetItem "in" Set	
			      | K "#in" Set	
   rule SetItem(K:K) in S:Set => K in S [structural, anywhere]
   rule K:K in S:Set => K #in S ==K true
     [structural, anywhere]
   rule K #in SetItem(K) S:Set => true
     [structural, anywhere]

endmodule

interface K-BAG-EXTRAS
	imports K-TECHNIQUE
	//imports IF-THEN-ELSE

	syntax Bag ::= "Bag" List{K}
				 | Bag "-Bag" Bag
	syntax Bool ::= K "in" Bag
				  | BagItem "in" Bag
endinterface

interface K-LIST-EXTRAS
	imports K-TECHNIQUE
	//imports BOOL

	syntax List ::= "List" List{K}

	syntax Int ::= "lengthList" List
endinterface

interface K-RESULT
	imports K-TECHNIQUE

	syntax K ::= KResult

	//op .List{K} : -> List{KResult} [ditto metadata "latex=(renameTo \\ensuremath{\\dotCt{List\\{K\\}}})"] .

endinterface

interface K-WRAPPERS-LABELS
	imports K-TECHNIQUE
	imports STRING

	syntax KLabel ::= "KLabel2KLabel" KLabel
					| "CellLabel2KLabel" CellLabel
					| "kList" String
					| "Bag2KLabel" Bag
					| "Set2KLabel" Set
					| "List2KLabel" List
					| "Map2KLabel" Map
					| "wrap-with"

endinterface

module K-DESTRUCTORS
	syntax KLabel ::= "getKLabel" K
  rule getKLabel(L:KLabel(_:List{K})) => L [structural, anywhere]

endmodule

interface K-WRAPPERS
	imports K-TECHNIQUE

	syntax K ::= "KLabel2K" KLabel
			   | "Celllabel2K" CellLabel
			   | "List{K}2K" List{K}
			   | "Set2K" Set
			   | "Bag2K" Bag
			   | "List2K" List
			   | "Map2K" Map
endinterface

interface K-EVAL
  imports K-TECHNIQUE
  syntax Bag ::= "#eval" Map          [cons(Bag1EvalSyn)]
  syntax Bag ::= "#evalHelper" Map    [cons(Bag1EvalHelperSyn)]
endinterface



interface K
  imports K-TECHNIQUE
  imports K-WRAPPERS
  imports K-WRAPPERS-LABELS
  //imports K-BUILTINS
  imports K-RESULT             // to express results syntactically
  imports K-RULES              // to write k rules with in-place rewriting
  imports K-CONFIG             // to specify the global configuration term
  imports K-EVAL
  imports K-POLYMORPHIC-VARIABLES // defines the ? polmorfic constant
  imports K-OPEN-CELLS            // defines open cells like <_>..._...</_> 
  imports K-CONTEXTS  
  imports K-DESTRUCTORS           // defines getKLabel and getList{K} for K
  //imports K-EXTRAS                // defines a KLabel substitution 
  imports K-LISTK-EXTRAS  
  imports K-LIST-EXTRAS  
  imports K-MAP-EXTRAS            // operations on Maps
  imports K-BAG-EXTRAS            // operations on Bags
  imports K-SET-EXTRAS            // operations on Sets
  //imports K-LATEX  
endinterface

interface  MODEL-CHECKER-INTERFACE
  imports #MODEL-CHECKER-INTERFACE
//  sorts #ModelCheckerState #Prop .
//  sort #ModelCheckResult .

//  op _LTL|=_ : #ModelCheckerState #Prop -> #Bool [frozen] .

  syntax #Bool ::= #ModelCheckerState "LTL|=" #Prop

endinterface
