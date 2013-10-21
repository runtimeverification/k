require "builtins/builtins.k"

module K-TECHNIQUE
	// all basic K syntax is in the SDF grammar directly,
	// but also needs to be defined in K - except for
	// a few things added by compiler passes.
	// Unfortunately, FlattenModules explicitly ignores
	// includes of K-TECHNIQUE and some other core modules,
	// so we have to declare things like isSet in less obvious places
	
	syntax KItem
endmodule

module K-LISTK-EXTRAS
  imports K-TECHNIQUE
  imports K-EQUAL-HOOKS
  
  syntax Bool ::= K "inKList" KList [function]
  syntax Bool ::= K "#inKList" KList [function] 
  rule K:K inKList L:KList => K #inKList L ==K true 
  rule K #inKList (_,,K:K,,_) => true 
endmodule

module K-MAP-EXTRAS
	imports K-TECHNIQUE
    imports K-SET-EXTRAS
	imports BOOL-HOOKS
	imports K-EQUAL-HOOKS

  syntax K ::= Map "(" K ")"  [function, klabel(deprecatedMapLookup)]
  rule (_ K1:K |-> K2:K)(K1) => K2

  syntax Map ::= Map "[" "undef" "/" KList "]"  [function]

  syntax Map ::= "Map" "(" KList "|->" KList ")"   [function]
  rule Map((K1:K => .KList),,_ |-> (K2:K => .KList),,_:K,,_) (. => K1 |-> K2) [structural]
  rule Map((K1:K => .KList),,_ |-> K2:K) (. => K1 |-> K2)
  rule Map(.KList |-> _) => .

  syntax Map ::= Map "[" KList "/" KList "]"  [function]
  rule (M:Map => M[K2/K1][K2'/K1'])[(K2:K,,K2':K => .KList),,_ 
                        /  (K1:K,,K1':K => .KList),,_]
   [structural, anywhere]
  rule M:Map[.KList / .KList] => M    
   [structural, anywhere]

  rule (M:Map K1:K |-> _:K)[K2:K / K1] => M K1 |-> K2 
    [structural, anywhere]
  rule M:Map[K2:K / K1:K] => M K1 |-> K2 
    when notBool(K1 in keys(M)) [structural, anywhere]
  
  rule M:Map[undef/ K:K,,Kl:KList] => M[undef/ K][undef/ Kl] when Kl =/=KList .KList [structural, anywhere]
  rule M:Map[undef/ .KList] => M [structural, anywhere]
  rule (M:Map K:K |-> _)[undef/ K] => M [structural, anywhere]

  syntax Map ::= Map "[" Map "]"   [function, cons(Map1UpdateMapWithMapSyn)]
  rule M:Map[M':Map K1:K |-> K2:K] => M[K2/K1][M'] [structural]
  rule M:Map[.Map] => M [structural]

//  syntax KList ::= Map "(" KList ")"
//  rule Map:Map((K1:K,,K2:K,,Ks:KList)) 
//    => Map(K1),,Map(K2),,Map(Ks) [structural]
//  rule Map:Map(.KList) => .KList [structural]

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

  syntax KLabel ::= "isSet"

//	syntax Set ::= "Set" KList
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
  rule Set2KTerm(S:Set) => Set2KTermAcc(S, #set(.KList))

  syntax K ::= Set2KTermAcc(Set, K)  [function]
  rule Set2KTermAcc((SetItem(K:K) => .Set)_, _(_,,(.KList => K)))
  rule Set2KTermAcc(.Set, K:K) => K

  
  

endmodule

module K-BAG-EXTRAS
	imports K-TECHNIQUE
	//imports IF-THEN-ELSE

//	syntax Bag ::= "Bag" KList
//				 | Bag "-Bag" Bag
//	syntax Bool ::= K "in" Bag
//				  | BagItem "in" Bag
endmodule

module K-LIST-EXTRAS
	imports K-TECHNIQUE
	//imports BOOL
	imports INT-HOOKS

//	syntax List ::= "List" KList

	syntax Int ::= "lengthList" List [function]

   rule lengthList ( _:ListItem L:List ) => 1 +Int lengthList L [structural, anywhere]
   rule lengthList .List => 0 [structural, anywhere]
   rule isKResult((_:KResult => .KList),, _:K,, _:KList)
   rule isKResult(.KList) => true
endmodule

module K-RESULT
	imports K-TECHNIQUE
	imports BOOL-HOOKS

	syntax K ::= KResult
	syntax KLabel ::= "isKResult"
        
           

	//op .KList : -> List{KResult} [ditto metadata "latex=(renameTo \\ensuremath{\\dotCt{List\\{K\\}}})"] .

endmodule

module K-WRAPPERS-LABELS
	imports K-TECHNIQUE

	syntax KLabel ::= "KLabel2KLabel" KLabel
					| "CellLabel2KLabel" CellLabel
					| "KList2KLabel" KList
					| "Bag2KLabel" Bag
					| "Set2KLabel" Set
					| "List2KLabel" List
					| "Map2KLabel" Map
					| "wrap-with"



  rule isSet(Set2KLabel(_)(.KList)) => true [predicate,anywhere]

endmodule

module K-DESTRUCTORS
	syntax KLabel ::= "getKLabel" K
  rule getKLabel(L:KLabel(_:KList)) => L [structural, anywhere]

endmodule

module K-WRAPPERS
	imports K-TECHNIQUE
// not used anymore
//	syntax K ::= KLabel2K (KLabel)		[klabel('KLabel2K_)]
//			   | Celllabel2K (CellLabel)[klabel('Celllabel2K_)] 
//			   | KList2K (KList)		[klabel('KList2K_)]
//			   | Set2K (Set)			[klabel('Set2K_)]
//			   | Bag2K (Bag)			[klabel('Bag2K_)]
//			   | List2K (List)			[klabel('List2K_)]
//			   | Map2K (Map)			[klabel('Map2K_)]
endmodule

module K-EVAL
  imports K-TECHNIQUE
  syntax Bag ::= "#eval" Map          [cons(Bag1EvalSyn)]
  syntax Bag ::= "#evalHelper" Map    [cons(Bag1EvalHelperSyn)]
endmodule

module K-BUILTINS
  syntax KLabel ::=  "#" K [builtinWrapper]
endmodule


module K-FRESH
  imports K-TECHNIQUE
  syntax Bool ::= "fresh" "(" K ")"  [cons(Bool1FreshSyn)]
endmodule

module K-FREZERS
  imports K-TECHNIQUE
  syntax KLabel ::= "#freezer" K
  syntax KLabel ::= "heat" | "heated" | "redex" | "cool"

  rule heat(heated(K:K)) => K 
  rule heat(heated(_,,K:K,,_)) => K
     [heat-choice]

  rule heat((redex(_:K,, K:K,, KL:KList) => K,,KL),,_)
    [owise]  
  rule heat((redex(K:K) => .KList),,_,,heated(_,,(.KList => K)))
    [owise]

  rule cool(K:K) => K [owise]
endmodule

module DEFAULT-CONFIGURATION
  imports K-TECHNIQUE
  configuration <k> $PGM:K </k>
endmodule
 
module K-TOKENS
  imports K-TECHNIQUE
  syntax KLabel ::= "#token"
  syntax K ::= isToken(K) [predicate]
  rule isToken(#token(_)) => true
endmodule

module K
  imports K-TECHNIQUE
  imports DEFAULT-CONFIGURATION
  imports K-WRAPPERS
  imports K-WRAPPERS-LABELS
  imports K-BUILTINS
  imports K-RESULT             // to express results syntactically
  // imports K-RULES              // to write k rules with in-place rewriting
  imports K-EVAL
  // imports K-CONTEXTS  
  imports K-DESTRUCTORS           // defines getKLabel and getKList for K
  //imports K-EXTRAS                // defines a KLabel substitution 
  imports K-FREZERS
  imports K-FRESH
  imports K-LISTK-EXTRAS  
  imports K-LIST-EXTRAS  
  imports K-MAP-EXTRAS            // operations on Maps
  imports K-BAG-EXTRAS            // operations on Bags
  imports K-SET-EXTRAS            // operations on Sets
  imports K-TOKENS
  //imports K-LATEX  
endmodule

