require meta-model
require substitution
kmod OCL-SEMANTICS is including META-MODEL  +  SUBSTITUTION 

//PRELIMINARIES
// values

//Collection values shall be wrapped bags of items. Items are wrapped ints, bools, 
//or pairs (instanceaName : ClassNameinstance names of class name
//the items are wrapped usng the predefined construction BagItem : K -> BagItem

syntax Collection ::=  val ( Bag ) 

// values of expressions
syntax Val ::= Collection | Int | Bool | String

syntax Exp ::= Val

// result of evaluation
syntax KResult ::= Val



syntax Val ::=  Id 
syntax Id ::= top | int | bool | string

// basic types

// for  attributes in metamodel instances
syntax K ::= typedElt ( K , Id )



// a few structural rule about sets of values
syntax Bag ::= Bag interBag Bag

rule  (v:BagItem V1:Bag) interBag (v:BagItem V2:Bag) => v (V1 interBag V2) [structural]
rule (v V1) interBag V2 =>  V1 interBag V2 if notBool (v  in  V2) [structural]
rule .Bag interBag V:Bag => .Bag [structural]
rule V interBag .Bag => .Bag [structural]


syntax Bag ::= Bag diffBag Bag
rule (v V1) diffBag (v V2) => V1 diffBag V2 [structural]
rule (v V1) diffBag V2 => v (V1 diffBag V2) if notBool (v  in  V2) [structural]
rule .Bag diffBag V:Bag => .Bag [structural]
rule V diffBag .Bag => V [structural]


//  card predicate
syntax Int ::= card ( Bag )
rule card(.Bag) => 0 [structural]
rule card(v:BagItem V:Bag) => 1 +Int card(V) [structural]


// subset predicate
syntax Bool ::= subset ( Bag , Bag ) 
rule subset(.Bag,  V) => true  [structural]
rule subset((v:BagItem V), V':Bag) =>
 if (v  in  V') then subset(V,V') else false fi  [structural]

//SEMANTICS
//identifiers evaluate to themselves: no rule needed

// ARITHMETICAL EXPRESSIONS
// "pure" expressions : only ints
rule A1:Int + A2:Int => A1 +Int A2  [structural]
rule A1 * A2 => A1 *Int A2  [structural]
rule A1 / A2 => A1 /Int A2 if notBool (A2 ==Int 0)  [structural]
rule (- A1) => -Int A1  [structural]


// "hybrid" expressions : ints and/or singleton collections
rule val(BagItem(A1)) + A2 => val(BagItem(A1 +Int A2)) [structural]
rule  A1 +  val(BagItem(A2)) => val(BagItem(A1 +Int A2)) [structural]
rule  val(BagItem(A1)) +  val(BagItem(A2)) => val(BagItem(A1 +Int A2)) [structural]
rule val(BagItem(A1)) / A2 => val(BagItem(A1 /Int A2)) if notBool (A2 ==Int 0)  [structural]
rule  A1 /  val(BagItem(A2)) => val(BagItem(A1 /Int A2)) if notBool (A2 ==Int 0) [structural]
rule  val(BagItem(A1)) /  val(BagItem(A2)) => val(BagItem(A1 /Int A2)) if notBool (A2 ==Int 0) [structural]
rule (-  val(BagItem(A1))) => val(BagItem(  -Int A1))  [structural]
rule (val(B:Bag) .size()) => card(B)  [structural]



// BOOLEAN
// "pure" expressions 
rule A1 < A2 => A1 <Int A2  [structural]
rule A1 <= A2 => A1 <=Int A2  [structural]
rule A1 > A2 => A1 >Int A2  [structural]
rule A1 >= A2 => A1 >=Int A2  [structural]
rule A1 = A2 => A1 ==Int A2  [structural]
rule A1 <> A2 => notBool (A1 ==Int A2)  [structural]
rule B1:Bool and B2:Bool => B1 andBool B2  [structural]
rule B1 or B2 => B1 orBool B2  [structural]
rule B1 implies B2 => (notBool B1) orBool B2  [structural] 
rule not B1 => notBool B1  [structural]

// "hybrid"
rule A1 < val(BagItem(A2)) => val(BagItem(A1 <Int A2))  [structural]
rule val(BagItem(A1)) < A2 => val(BagItem(A1 <Int A2))  [structural]
rule val(BagItem(A1)) < val(BagItem(A2)) => val(BagItem(A1 <Int A2))  [structural]


rule A1 <= val(BagItem(A2)) => val(BagItem(A1 <=Int A2))  [structural]
rule val(BagItem(A1)) <= A2 => val(BagItem(A1 <=Int A2))  [structural]
rule val(BagItem(A1)) <= val(BagItem(A2)) => val(BagItem(A1 <=Int A2))  [structural]

rule A1 >= val(BagItem(A2)) => val(BagItem(A1 >=Int A2))  [structural]
rule val(BagItem(A1)) >= A2 => val(BagItem(A1 >=Int A2))  [structural]
rule val(BagItem(A1)) >= val(BagItem(A2)) => val(BagItem(A1 >=Int A2))  [structural]

rule A1 = val(BagItem(A2)) => val(BagItem(A1 ==Int A2))  [structural]
rule val(BagItem(A1)) = A2 => val(BagItem(A1 ==Int A2))  [structural]
rule val(BagItem(A1)) = val(BagItem(A2)) => val(BagItem(A1 ==Int A2))  [structural]

rule A1 <> val(BagItem(A2)) => val(BagItem(notBool(A1 ==Int A2)))  [structural]
rule val(BagItem(A1))  <> A2  => val(BagItem(notBool(A1 ==Int A2)))  [structural]
rule val(BagItem(A1))  <>  val(BagItem(A2))  => val(BagItem(notBool(A1 ==Int A2)))  [structural]


rule B1:Bool and val(BagItem(B2:Bool)) => val(BagItem(B1 andBool B2))  [structural]
rule val(BagItem(B1:Bool)) and B2:Bool => val(BagItem(B1 andBool B2))  [structural]
rule val(BagItem(B1:Bool)) and val(BagItem(B2:Bool)) => val(BagItem(B1 andBool B2))  [structural]


rule B1:Bool or val(BagItem(B2:Bool)) => val(BagItem(B1 orBool B2))  [structural]
rule val(BagItem(B1:Bool)) or B2:Bool => val(BagItem(B1 orBool B2))  [structural]
rule val(BagItem(B1:Bool)) or val(BagItem(B2:Bool)) => val(BagItem(B1 orBool B2))  [structural]


rule B1:Bool implies val(BagItem(B2:Bool)) => val(BagItem( (notBool B1) orBool B2))  [structural]
rule val(BagItem(B1:Bool)) implies B2:Bool => val(BagItem( (notBool B1) orBool B2))  [structural]
rule val(BagItem(B1:Bool)) implies val(BagItem(B2:Bool)) => val(BagItem( (notBool B1) orBool B2))  [structural]





rule not val(BagItem(B1)) => val(BagItem(notBool B1))  [structural]




rule val(C1:Bag) includes val(C2:Bag) => subset(C2,C1)  [structural]
rule val(C1:Bag) excludes val(.Bag) => true  [structural]
rule val(Bg:BagItem C1:Bag) excludes val(Bg:BagItem C2:Bag) => 
if (Bg in C1) 
then false 
else  val(Bg:BagItem C1:Bag) excludes val(C2:Bag) 
fi  [structural]

// equality.  Note that equality of pairs (instanceName : instanceClass)
// is enough to ensure that the corresponding instances (incl attributes)
// are indeed equal, since by hypothesis there is at most one pair 
// (instanceName : instanceClass) per model
rule (val(C1) = val(C2)) => C1 ==Bool C2 [structural]
rule (Str1 = Str2) => Str1 ==Bool Str2 [structural]
rule (val(BagItem(Str1)) = Str2) => Str1 ==Bool Str2 [structural]
rule (Str1 = val(BagItem(Str2))) => Str1 ==Bool Str2 [structural]

rule (A1 = A2) =>  A1 ==Int A2 [structural]
rule (val(BagItem(A1)) = A2) =>  A1 ==Int A2 [structural]
rule (A1 = val(BagItem(A2))) =>  A1 ==Int A2 [structural]

rule (B1 = B2:Bool) =>  B1 ==Bool B2 [structural]
rule (val(BagItem(B1)) = B2:Bool) =>  B1 ==Bool B2 [structural]
rule (B1 = val(BagItem(B2:Bool))) =>  B1 ==Bool B2 [structural]

rule (Id1:Id = Id2:Id) => Id1 ==Bool Id2 [structural]


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
rule val(BagItem(Str1)) ++ Str2 => val(BagItem(Str1 +String Str2)) [structural]
rule Str2 ++ val(BagItem(Str1)) => val(BagItem(Str1 +String Str2)) [structural]
rule val(BagItem(Str1)) ++ val(BagItem(Str2))   => val(BagItem(Str1 +String Str2)) [structural]

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
 <temp_> 
  .Bag => B
 <_/temp>
[structural]

//including

rule <k> val(C1) Including I:Int  =>  val(C1 BagItem(I)) <_/k> [structural]
rule <k> val(C1) Including Str1  => val(C1 BagItem(Str1)) <_/k> [structural]
rule <k> val(C1) Including bbb:Bool =>  val(C1 BagItem(bbb)) <_/k> [structural]
rule <k> val(C1) Including val(C2)  =>   val(C1) union val(C2) <_/k> [structural]


//union, intersection, difference
// "pure"
rule <k> val(C1) union val(C2)   => val(C1 C2) <_/k> [structural]
rule <k> val(C1) inter val(C2) => val(C1 interBag C2) <_/k> [structural]
rule <k> val(C1) diff val(C2) => val(C1 diffBag C2)  <_/k> [structural]



//collect: by analogy with forAll, exists
rule <k> val(.Bag) ->collect(_|_) => val(.Bag)  <_/k> [structural]

rule <k>
 val(( BI:BagItem B:Bag)) ->collect( Var:Id | CEXP:Exp ) =>
   (val(B) ->collect( Var | CEXP))  Including CEXP[open(BI)/Var]
<_/k>
 [structural]

syntax Exp ::=  Exp `Including Exp [strict] // add 2nd arg (element) to 1st arg collection


//select
// base case: when there is nothing select: take result from temp cell

rule <k>
val(.Bag) ->select(_|_) => val(B) <_/k>
<comp>
 B => .
</comp>
[structural]


syntax Id ::= toto1 | toto2


syntax K ::= `@temp ( K ) [strict]

//inductive step : place the result in wrapped form at the head of the computation


rule <k>( val(( BI B)) ->select( Var| BEXP:Exp )) => 
@temp(if BEXP[open(BI)/Var] then val(BI) else val(.Bag) endif ) 
~> (val(B) ->select( Var | BEXP))
<_/k>
//[structural]


/* 
rule <k>( val(( BI1:BagItem BI2:BagItem B)) ->select( Var| BEXP:Exp )) => 
@temp(if BEXP[open(BI2)/Var] then val(BI2) else val(.Bag) endif ) ~> toto1 ~>
@temp(if BEXP[open(BI1)/Var] then val(BI1) else val(.Bag) endif )  
~> (val(B) ->select( Var | BEXP))
<_/k>
// [structural]
*/
// and when it's evaluated, place result in temp cell


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
syntax  Exp ::= oclType ( Exp ) [strict]

 
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

