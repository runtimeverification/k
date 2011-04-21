require ../../../../k-prelude

kmod VALUES is including  K + PL-ID + PL-INT + PL-STRING
syntax Collection ::=  val ( Bag ) 

// values of expressions
syntax Val ::= Collection | Int | Bool | String
// basic types
syntax Id ::= top | int | bool | string 

// typed values
syntax K ::= typedElt ( Val , Id )

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


// general rules for mixing scalar and non-scalar values
// for binary operators
//(*)
rule KL:KLabel(val(BagItem(Val1:Val)),,val(BagItem(Val2:Val))) => KL:KLabel(Val1,, Val2) 
if (binaryOp(KL))  andBool isScalar((Val1)) andBool isScalar((Val2))
[structural]

rule KL:KLabel( Val1:Val,,val(BagItem(Val2:Val))) => KL:KLabel(Val1,, Val2) 
if (binaryOp(KL))  
andBool isScalar((Val1)) andBool isScalar((Val2))
[structural]


rule KL:KLabel( val(BagItem(Val1:Val)),,Val2:Val) => KL:KLabel(Val1,, Val2) 
if (binaryOp(KL))  andBool isScalar((Val1)) andBool isScalar((Val2))
[structural]

// "critical pair"? with previous one : C1 = BagItem(Val1)
// solved by (*)
rule KL:KLabel( val(C1:Bag),,Val2:Val) => KL:KLabel(val(C1),, val(BagItem(Val2)))
if (binaryOp(KL))  andBool  isScalar((Val2))
[structural]


rule KL:KLabel( Val1,, val(C2:Bag)) => KL:KLabel(val(BagItem(Val1)),,val(C2))
if (binaryOp(KL))  andBool  isScalar((Val1))
[structural]

// for unary operators
syntax Bool ::= binaryOp ( KLabel )  |  unaryOp ( KLabel )

macro binaryOp(KL) =   
((KL ==Bool  '_+_) orBool  
(KL ==Bool  '_*_) orBool 
(KL ==Bool  '_/_) orBool 
(KL ==Bool  '_<_) orBool  
(KL ==Bool  '_<=_) orBool  
(KL ==Bool  '_>_) orBool  
(KL ==Bool  '_>=_) orBool  
(KL ==Bool  '_and_) orBool
(KL ==Bool  '_or_) orBool
(KL ==Bool  '_implies_) orBool 
(KL ==Bool  '_=_) orBool
(KL ==Bool  '_++_) orBool
(KL ==Bool  '_union_))

macro unaryOp(KL) = 
(
(KL ==Bool '-_) orBool
(KL ==Bool 'not_) 
)



rule KL:KLabel(val(BagItem(Val1:Val))) => KL:KLabel(Val1) 
if (unaryOp(KL))  
andBool isScalar((Val1)) 
[structural]


// scalar values

syntax Bool ::= isScalar ( Val )
rule isScalar(I:Int) => true [structural]
rule isScalar(bbb:Bool) => true [structural]
rule isScalar(Str:String) => true [structural]
rule isScalar(val(C1)) => false [structural]




endkm