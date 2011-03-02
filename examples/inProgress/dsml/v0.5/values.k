require meta-model

kmod VALUES is including META-MODEL
syntax Collection ::=  val ( Bag ) 

// values of expressions
syntax Val ::= Collection | Int | Bool | String
// basic types
syntax Id ::= top | int | bool | string 
// and id's for class types, are possible values of expressions (the oclType function)
syntax Val ::=  Id 

syntax Exp ::= Val

// result of evaluation
syntax KResult ::= Val



//  card predicate
syntax Int ::= card ( Bag )
rule card(.Bag) => 0 [structural]
rule card(v:BagItem V:Bag) => 1 +Int card(V) [structural]


// subset predicate
syntax Bool ::= subset ( Bag , Bag ) 
rule subset(.Bag,  V) => true  [structural]
rule subset((v:BagItem V), V':Bag) =>
 if (v  in  V') then subset(V,V') else false fi  [structural]
endkm