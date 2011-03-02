require values
require substitution
kmod OCL-SEMANTICS is including VALUES  +  SUBSTITUTION 


//SEMANTICS
//identifiers evaluate to themselves: no rule needed
// general rules for mixing scalar and non-scalar values

// for binary operators

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


rule KL:KLabel( val(C1),,Val2:Val) => KL:KLabel(val(C1),, val(BagItem(Val2)))
if (binaryOp(KL))  andBool  isScalar((Val2))
[structural]


rule KL:KLabel( Val1,, val(C2)) => KL:KLabel(val(BagItem(Val1)),,val(C2))
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


// ARITHMETICAL EXPRESSIONS
// "pure" expressions : only ints
rule A1:Int + A2:Int => A1 +Int A2  [structural]
rule A1 * A2 => A1 *Int A2  [structural]
rule A1 / A2 => A1 /Int A2 if notBool (A2 ==Int 0)  [structural]
rule (- A1) => -Int A1  [structural]

rule (val(B:Bag) .size()) => card(B)  [structural]
rule (I:Int .size()) => 1  [structural]
rule (bbb:Bool .size()) => 1  [structural]
rule (Str:String .size()) => 1  [structural]

syntax Bool ::= isScalar ( Exp )
rule isScalar(I) => true [structural]
rule isScalar(bbb) => true [structural]
rule isScalar(Str) => true [structural]
rule isScalar(val(C1)) => false [structural]


rule KL:KLabel(val(BagItem(Val1:Val))) => KL:KLabel(Val1) 
if (unaryOp(KL))  
andBool isScalar((Val1)) 
[structural]



// BOOLEAN
// "pure" expressions 
rule A1 < A2 => A1 <Int A2  [structural]
rule A1 <= A2 => A1 <=Int A2  [structural]
rule A1 > A2 => A1 >Int A2  [structural]
rule A1 >= A2 => A1 >=Int A2  [structural]

rule true and E:Exp => E  [structural]
rule false and E => false  [structural]

rule true or E => true  [structural]
rule false or E => E  [structural]

rule true implies E => E  [structural]
rule false implies E => true  [structural]

rule not B1:Bool => notBool B1  [structural]


// equality,  for all types

rule (Id1:Id = Id2:Id) => Id1 ==Bool Id2 [structural]
rule A1 = A2 => A1 ==Int A2  [structural]
rule (Str1 = Str2) => Str1 ==Bool Str2 [structural]
rule (B1 = B2:Bool) =>  B1 ==Bool B2 [structural]
rule (val(C1) = val(C2)) => C1 ==Bool C2 [structural]


//includes, excludes
rule val(C1:Bag) includes val(C2:Bag) => subset(C2,C1)  [structural]
rule val(C1:Bag) excludes val(.Bag) => true  [structural]
rule val(Bg:BagItem C1:Bag) excludes val(Bg':BagItem C2:Bag) => 
if (Bg ==Bool Bg') 
then false 
else  val(Bg:BagItem C1:Bag) excludes val(C2:Bag) 
fi  [structural]


// isEmpty
rule isEmpty(val(.Bag)) => true [structural]
rule isEmpty(val(BagIt:BagItem _)) => false  [structural]

//forAll
// overloading the substitution operator to  expressions
syntax Exp ::=  Exp [ K / Id ] [ditto]
// base case
rule <k> val(.Bag) ->forAll(_| _) => true <_/k> [structural]

// inductive step
rule <k>
val(( BI:BagItem B:Bag)) ->forAll( Var:Id | BEXP:Exp ) => 
if 
BEXP[open(BI)/Var] 
then val(B) ->forAll( Var | BEXP)
else false
endif 
<_/k> 
[structural]

// the value replacing the variable need to be "opened"
syntax K ::= open ( BagItem )
rule open(BagItem(kv:K)) => kv [structural]

//exists 
rule  <k> val(.Bag) ->exists(_| _) => false <_/k> [structural]
rule <k>
val(( BI:BagItem B:Bag)) ->exists( Var:Id | BEXP:Exp ) => 
if  BEXP[open(BI)/Var] 
then true 
else val(B) ->exists( Var | BEXP)
endif 
<_/k> 
[structural]

//STRINGS
//"pure"
rule Str1:String ++ Str2:String => Str1 +String Str2 [structural]
//"hybrid"


// COLLECTIONS
// rule for empty
rule <k> empty => val(.Bag) <_/k> [structural]

// rules Class .allInstances
rule <k> allInstances(Cls:Id) => val(collectInstanceNames(Cls, INST:Bag)) <_/k>  
       //NB one model only!
       <models>
         <model> <modelName> MN:Id </modelName> // 
            INST
         </model>
      </models>
 [structural] 

//collectInstances function: collects instances of class Cls
syntax Bag ::= collectInstanceNames ( Id , Bag ) 
rule collectInstanceNames(Cls, .Bag) => .Bag [structural]

rule collectInstanceNames(Cls, 
                        (<instance> 
                             <instName> INAME:Id </instName> 
                             <ofClass> Cls </ofClass>
                             <attributes> ATTR:Map </attributes>
                         </instance> 
                        REST:Bag
                       )
                     )
                      =>    BagItem(INAME : Cls)
                      collectInstanceNames(Cls, REST) [structural]

rule collectInstanceNames(Cls, 
                        (<instance> 
                             <instName> INAME </instName> 
                             <ofClass> Cls':Id </ofClass>
                             <attributes> ATTR </attributes>
                         </instance> REST:Bag))
                        =>  collectInstanceNames(Cls, REST)
                        if notBool (Cls ==Bool Cls') [structural]

// ":"
rule <k> INAME : Cls => val(BagItem(INAME : Cls)) <_/k> [structural]


// rule for CExp # Id [strict] 
// NB all elements in CExp are assumed to have the attribute Id
// may write a typechecker in the future



// when finished, the bag of instances whose AT we are trying to get is empty: 
// take result from temp cell and dissolve
rule <k> (val(.Bag) # AT) => val(B:Bag) <_/k> <temp> B => . </temp> 
[structural]



// when not finished, the bag of instances whose AT we are trying to get is nonempty
// the value of AT is stored in temp cell
// CARE : all attribute values should be collections !!!!
rule <k>  val(BagItem(INAME : Cls) REMAINING:Bag) # AT:Id
       => val(REMAINING) # AT
 <_/k>   
<models>
   <model_>
      <instance> 
          <instName> INAME </instName>
          <ofClass> Cls </ofClass>
          <attributes_> AT |-> typedElt(val(B:Bag),T:Id) <_/attributes> 
      </instance> 
   <_/model>
</models>
 <temp_> // loc n = expression, loc n+1 = its value
  .Bag => B
 <_/temp>
[structural]


//union: also with basic types
rule <k> val(C1) union val(C2)   => val(C1 C2) <_/k> [structural]
rule <k> Val1 union Val2   => val(BagItem(Val1) BagItem(Val2)) <_/k> 
if isScalar((Val1)) andBool isScalar((Val2))
[structural]

//rule <k> val(C1) union I:Int  => val(C1 BagItem(I)) <_/k> [structural]
//rule <k>  I:Int union val(C1)  => val(C1 BagItem(I)) <_/k> [structural]

//rule <k> val(C1) union Str1  => val(C1 BagItem(Str1)) <_/k> [structural]
//rule <k>  Str1 union val(C1)   => val(C1 BagItem(Str1)) <_/k> [structural]

//rule <k> val(C1) union bbb:Bool  => val(C1 BagItem(bbb)) <_/k> [structural]
//rule <k>  bbb union val(C1)  => val(C1 BagItem(bbb)) <_/k> [structural]


//collect: by analogy with forAll, exists
rule <k> val(.Bag) ->collect(_|_) => val(.Bag)  <_/k> [structural]

rule <k>
 val(( BI:BagItem B:Bag)) ->collect( Var:Id | CEXP:Exp ) =>
   (val(B) ->collect( Var | CEXP))  union CEXP[open(BI)/Var]
<_/k>
 [structural]

/*
syntax Exp ::=  Exp `Including Exp [strict] // add 2nd arg (element) to 1st arg collection

rule <k> val(C1) Including I:Int  =>  val(C1 BagItem(I)) <_/k> [structural]
rule <k> val(C1) Including Str1  => val(C1 BagItem(Str1)) <_/k> [structural]
rule <k> val(C1) Including bbb:Bool =>  val(C1 BagItem(bbb)) <_/k> [structural]
rule <k> val(C1) Including val(C2)  =>   val(C1) union val(C2) <_/k> [structural]
*/

//select
// base case: when there is nothing select: take result from comp cell

rule <k>
val(.Bag) ->select(_|_) => val(B) <_/k>
<comp>
 B => .
</comp>
[structural]





syntax K ::= `@temp ( K ) [strict]

//inductive step : place the result in wrapped form at the head of the computation


rule <k>( val(( BI B)) ->select( Var| BEXP:Exp )) => 
@temp(if BEXP[open(BI)/Var] then val(BI) else val(.Bag) endif ) 
~> (val(B) ->select( Var | BEXP))
<_/k>
[structural]


rule
<k> @temp(val(.Bag))  => . <_/k> [structural]



rule
<k> @temp(val(BI))  => . <_/k>
<comp_> 
. => BI
<_/comp>
//[structural]



// let : just substitution
rule <k> let  X:Id =  CEXP1 in CEXP2  endlet => CEXP2[CEXP1/X] <_/k> [structural]

// if
rule <k> if true then CEXP1:Exp else CEXP2:Exp endif => CEXP1 <_/k> [structural]
rule <k> if false then CEXP1 else CEXP2 endif => CEXP2 <_/k> [structural]

rule <k> if val(BagItem(true)) then CEXP1:Exp else CEXP2:Exp endif => CEXP1 <_/k> [structural]
rule <k> if val(BagItem(false)) then CEXP1 else CEXP2 endif => CEXP2 <_/k> [structural]








//oclType
// for ariyhmetical, boolean, string expressions: just returns their basic type
// for collections: computes the lub (least upper bound) of types of elements inside
//syntax  Exp ::= oclType ( Exp ) [strict]

 
// arithmetical, boolean, string
rule oclType(A1) => int [structural]
rule oclType(B1) => bool [structural]
rule oclType(Str1) => string [structural]

// collections
// the lattice is : top - everything (flat)
// will change in the future when we add inheritance

rule oclType(val(BagItem (A1))) => int  [structural]
rule oclType(val(BagItem (B1))) => bool  [structural]
rule oclType(val(BagItem (Str1))) => string  [structural]

rule  oclType(val(BagItem (A1) BagItem(A2) B:Bag)) =>
      oclType(val(BagItem(A2) B:Bag)) [structural]

rule  oclType(val(BagItem (B1) BagItem(B2) B:Bag)) =>
      oclType(val(BagItem(B2) B:Bag)) [structural]

rule  oclType(val(BagItem (Str1) BagItem(Str2) B:Bag)) =>
      oclType(val(BagItem(Str2) B:Bag)) [structural]


rule  oclType(val(BagItem (A1) BagItem(B1) B:Bag)) =>
      top [structural]

rule  oclType(val(BagItem (A1) BagItem(Str1) B:Bag)) =>
      top [structural]

rule  oclType(val(BagItem (A1) BagItem(_ : _) B:Bag)) =>
      top [structural]

rule  oclType(val(BagItem (B1) BagItem(Str1) B:Bag)) =>
      top [structural]

rule  oclType(val(BagItem (B1) BagItem(_ : _) B:Bag)) =>
      top [structural]

rule oclType(val(BagItem (_ : Cls))) => Cls  [structural]


rule oclType (val(BagItem (_: Cls) BagItem (Ins2:Id : Cls)  B:Bag))
 => oclType (val(BagItem (Ins2 : Cls)  B:Bag))  [structural]



// for now, the lub of two distinct classes is just "top"
// will change in the future when we add inheritance
rule oclType (val(BagItem (_ : Cls) BagItem (_ : Cls':Id)  _))
=> top if notBool (Cls ==Bool Cls')  [structural]


rule oclType(val(.Bag)) => top [structural]
 
endkm

