require "builtins/builtins.k"

interface K-TECHNIQUE
	// all in SDF directly
endinterface

module K-LISTK-EXTRAS
  imports K-TECHNIQUE
  imports K-EQUAL-HOOKS
  
  syntax Bool ::= K "inList{K}" List{K} [function]
  syntax Bool ::= K "#inList{K}" List{K} [function] 
  rule K:K inList{K} L:List{K} => K #inList{K} L ==K true 
  rule K #inList{K} (_,,K:K,,_) => true 
endmodule

module K-MAP-EXTRAS
	imports K-TECHNIQUE
    imports K-SET-EXTRAS
	imports BOOL-HOOKS
	imports K-EQUAL-HOOKS

  syntax K ::= Map "(" K ")"  [function]
  rule (_ K1:K |-> K2:K)(K1) => K2

  syntax Map ::= Map "[" "undef" "/" List{K} "]"  [function]

  syntax Map ::= "Map" "(" List{K} "|->" List{K} ")"   [function]
  rule Map((K1:K => .List{K}),,_ |-> (K2:K => .List{K}),,_:K,,_) (. => K1 |-> K2) [structural]
  rule Map((K1:K => .List{K}),,_ |-> K2:K) (. => K1 |-> K2)
  rule Map(.List{K} |-> _) => .

  syntax Map ::= Map "[" List{K} "/" List{K} "]"  [function]
  rule (M:Map => M[K2/K1][K2'/K1'])[(K2:K,,K2':K => .List{K}),,_ 
                        /  (K1:K,,K1':K => .List{K}),,_]
   [structural, anywhere]

  rule (M:Map K1:K |-> _:K)[K2:K / K1] => M K1 |-> K2 
    [structural, anywhere]
  rule M:Map[K2:K / K1:K] => M K1 |-> K2 
    when notBool(K1 in keys(M)) [structural, anywhere]
  
  rule M:Map[undef/ K:K,,Kl:List{K}] => M[undef/ K][undef/ Kl] when Kl =/=List{K} .List{K} [structural, anywhere]
  rule M:Map[undef/ .List{K}] => M [structural, anywhere]
  rule (M:Map K:K |-> _)[undef/ K] => M [structural, anywhere]

  syntax Map ::= Map "[" Map "]"   [function, cons(Map1UpdateMapWithMapSyn)]
  rule M:Map[M':Map K1:K |-> K2:K] => M[K2/K1][M'] [structural]
  rule M:Map[.Map] => M [structural]

//  syntax List{K} ::= Map "(" List{K} ")"
//  rule Map:Map((K1:K,,K2:K,,Ks:List{K})) 
//    => Map(K1),,Map(K2),,Map(Ks) [structural]
//  rule Map:Map(.List{K}) => .List{K} [structural]

	syntax Set ::= "keys" Map  [function]

  rule keys . => . [structural]
  rule (keys ((K:K |->_  => .) _)) (. => SetItem(K)) [structural]

	syntax Set ::= "values" Map  [function]

  rule values . => . [structural]
  rule (values ((_ |-> K:K  => .) _)) (. => SetItem(K)) [structural]

  syntax Bool ::= "$hasMapping" "(" Map "," K ")" [function,maudeop("$hasMapping")]
  syntax Bool ::= "#hasMapping" "(" Map "," K ")" [function, maudeop("#hasMapping")]
  rule $hasMapping(M:Map,K:K) => #hasMapping(M,K) ==K true

  rule #hasMapping(_:Map K:K |-> _:K,K) => true


// The following are used in pattern-matching.k

  syntax K ::= #map(Map)
  syntax Bool ::= #isMapInK(K)     [function]
  syntax Map  ::= #getMapFromK(K)  [function]
  rule #isMapInK(#map(_)) => true
  rule #getMapFromK(#map(M:Map)) => M

endmodule

module K-SET-EXTRAS
	imports K-TECHNIQUE
	imports BOOL-HOOKS
	imports K-EQUAL-HOOKS

//	syntax Set ::= "Set" List{K}
        syntax Set ::= Set "-Set" Set  [function, latex({#1}-_{\it Set}{#2})]
  rule S1:Set -Set (SI1:SetItem SI2:SetItem S2:Set)
    => ((S1 -Set SI1) -Set SI2) -Set S2
  rule S1:Set -Set . => S1 
  rule (SI:SetItem S:Set) -Set SI => S
  rule S:Set -Set SI:SetItem => S when SI in S ==Bool false //  [owise]

	syntax Bool ::= K "in" Set   [function, klabel(inSet)]
			      | SetItem "in" Set   [function, klabel(kInSet)]	
			      | K "#inSet" Set   [function]	
   rule SetItem(K:K) in S:Set => K in S [structural, anywhere]
   rule K:K in S:Set => K #inSet S ==K true
     [structural, anywhere]
   rule K:K #inSet SetItem(K) _:Set => true
     [structural, anywhere]

   rule (SetItem(K:K) S1:Set) -Set (SetItem(K:K) S2:Set) => S1 -Set (SetItem(K:K) S2) [structural, anywhere]
   rule (SetItem(K:K) S1:Set) -Set S2:Set => SetItem(K:K) (S1 -Set S2) when notBool K in S2 [structural, anywhere]
   rule .Set -Set _:Set => .Set [structural, anywhere]


  syntax Set ::= intersectSet(Set, Set) [function]
  rule intersectSet(A:Set, B:Set) => A -Set (A -Set B)

  syntax Bool ::= isEmptySet(Set) [function]
  rule isEmptySet(A:Set) => (A ==Set .Set)

  syntax KLabel ::= "#set"

  syntax K ::= Set2KTerm(Set)        [function]
  rule Set2KTerm(S:Set) => Set2KTermAcc(S, #set(.List{K}))

  syntax K ::= Set2KTermAcc(Set, K)  [function]
  rule Set2KTermAcc((SetItem(K:K) => .Set)_, _(_,,(.List{K} => K)))
  rule Set2KTermAcc(.Set, K:K) => K

  
  

endmodule

interface K-BAG-EXTRAS
	imports K-TECHNIQUE
	//imports IF-THEN-ELSE

//	syntax Bag ::= "Bag" List{K}
//				 | Bag "-Bag" Bag
//	syntax Bool ::= K "in" Bag
//				  | BagItem "in" Bag
endinterface

interface K-LIST-EXTRAS
	imports K-TECHNIQUE
	//imports BOOL
	imports INT-HOOKS

//	syntax List ::= "List" List{K}

	syntax Int ::= "lengthList" List [function]

   rule lengthList ( ListItem(_) L:List ) => 1 +Int lengthList L [structural, anywhere]
   rule lengthList .List => 0 [structural, anywhere]
        rule isKResult((K1:KResult => .List{K}),, _:K,, _:List{K})
endinterface

module K-RESULT
	imports K-TECHNIQUE
	imports BOOL-HOOKS

	syntax K ::= KResult
        
           

	//op .List{K} : -> List{KResult} [ditto metadata "latex=(renameTo \\ensuremath{\\dotCt{List\\{K\\}}})"] .

endmodule

interface K-WRAPPERS-LABELS
	imports K-TECHNIQUE

	syntax KLabel ::= "KLabel2KLabel" KLabel
					| "CellLabel2KLabel" CellLabel
					| "List{K}2KLabel" List{K}
					| "Bag2KLabel" Bag
					| "Set2KLabel" Set
					| "List2KLabel" List
					| "Map2KLabel" Map
					| "wrap-with"



  syntax KLabel ::= "isSet"
  rule isSet(Set2KLabel(_)(.List{K})) => true [anywhere]

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

module K-BUILTINS
  syntax KLabel ::=  "#" K
endmodule


interface K-FRESH
  imports K-TECHNIQUE
  syntax Bool ::= "fresh" "(" K ")"  [cons(Bool1FreshSyn)]
endinterface

interface K-FREZERS
  imports K-TECHNIQUE
  syntax KLabel ::= "#freezer" K
endinterface

interface K
  imports K-TECHNIQUE
  imports K-WRAPPERS
  imports K-WRAPPERS-LABELS
  imports K-BUILTINS
  imports K-RESULT             // to express results syntactically
  imports K-RULES              // to write k rules with in-place rewriting
  imports K-EVAL
  imports K-CONTEXTS  
  imports K-DESTRUCTORS           // defines getKLabel and getList{K} for K
  //imports K-EXTRAS                // defines a KLabel substitution 
  imports K-FREZERS
  imports K-FRESH
  imports K-LISTK-EXTRAS  
  imports K-LIST-EXTRAS  
  imports K-MAP-EXTRAS            // operations on Maps
  imports K-BAG-EXTRAS            // operations on Bags
  imports K-SET-EXTRAS            // operations on Sets
  //imports K-LATEX  
endinterface

