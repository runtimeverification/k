require meta-model
require substitution
kmod OCL-SEMANTICS is including META-MODEL  +  SUBSTITUTION + K-CONDITION-SEARCH

//PRELIMINARIES
// values

//for instance name of certain class

// values are either collection values, integers, or Booleans
syntax KResult ::= ValCExp | Int | Bool | String

// collection values are  wrapped bags of wrapped ints, bools, or instance names of class name
// the wrappped ints etc use the predefined construction BagItem : K -> BagItem
syntax ValCExp ::=  val ( Bag ) 

// return value of Collection expression

syntax CExp ::= ValCExp



// type names occuring in any model (independent of metamodel)
syntax Id ::= int | bool | string | colInt | colBool | colString | colInst

// for  attributes in metamodel instances
syntax K ::= typedElt ( K , Id )



// a few structural rule about sets of values
syntax Bag ::= Bag interBag Bag

rule  (v:BagItem V1:Bag) interBag (v:BagItem V2:Bag) => v (V1 interBag V2) [structural]
rule (v V1) interBag V2 =>  V1 interBag V2 if notBool (v  inBag  V2) [structural]
rule .Bag interBag V:Bag => .Bag [structural]
rule V interBag .Bag => .Bag [structural]


syntax Bag ::= Bag diffBag Bag
rule (v V1) diffBag (v V2) => V1 diffBag V2 [structural]
rule (v V1) diffBag V2 => v (V1 diffBag V2) if notBool (v  inBag  V2) [structural]
rule .Bag diffBag V:Bag => .Bag [structural]
rule V diffBag .Bag => V [structural]

// this exists in K-PRELUDE
syntax Bool ::= BagItem inBag  Bag
rule v  inBag  (v V) => true [structural]
rule v  inBag  (v':BagItem V) => v  inBag  V if notBool(v ==Bool v') [structural] 
rule v  inBag  .Bag => false [structural]

//  card predicate
syntax Int ::= card ( Bag )
rule card(.Bag) => 0 [structural]
rule card(v:BagItem V:Bag) => 1 +Int card(V) [structural]


// subset predicate
syntax Bool ::= subset ( Bag , Bag ) 
rule subset(.Bag,  V) => true  [structural]
rule subset((v:BagItem V), V':Bag) =>
 if (v  inBag  V') then subset(V,V') else false fi  [structural]

// structural 
//SEMANTICS
// semantics of arithmetical expressions
rule A1:Int + A2:Int => A1 +Int A2  [structural]
rule A1 * A2 => A1 *Int A2  [structural]
rule A1 / A2 => A1 /Int A2 if notBool (A2 ==Int 0)  [structural]
rule (- A1) => -Int A1  [structural]
rule (val(B:Bag) .size()) => card(B)  [structural]


// semantics of Boolean expressions

rule A1 < A2 => A1 <Int A2  [structural]
rule A1 <= A2 => A1 <=Int A2  [structural]
rule A1 > A2 => A1 >Int A2  [structural]
rule A1 >= A2 => A1 >=Int A2  [structural]
rule A1 = A2 => A1 ==Int A2  [structural]
rule A1 <> A2 => notBool (A1 ==Int A2)  [structural]
rule B1:Bool and B2:Bool => B1 andBool B2  [structural]
rule B1 or B2 => B1 orBool B2  [structural]
rule B1 implies B2 => (notBool B1) orBool B2  [structural] 
rule B1 equiv B2 => B1 ==Bool B2  [structural]
rule not B1 => notBool B1  [structural]



rule val(C1:Bag) in val(C2:Bag) => subset(C1,C2)  [structural]
rule val(C1:Bag) in* val(C2:Bag) => subset(C1,C2) andBool (card(C1) <Int card(C2))  [structural]
rule val(C1) notin val(C2) => notBool (subset(C1,C2))  [structural]
rule val(C1) notin* val(C2) => notBool (subset(C1,C2) andBool (card(C1) <Int card(C2)))
 [structural]

// equality.  Note that equality of pairs (instanceName : instanceClass)
// is enough to ensure that the corresponding instances (incl attributes)
// are indeed equal, since by hypothesis there is at most one pair 
// (instanceName : instanceClass) per model
rule (val(C1) = val(C2)) => C1 ==Bool C2 [structural]

// isEmpty
rule isEmpty(val(.Bag)) => true [structural]
rule isEmpty(val(BagIt:BagItem _)) => false  [structural]

//forAll
// overloading the substitution operator to Boolean expressions
syntax BExp ::=  BExp [ K / Id ] [ditto]
// base case
rule <k> val(.Bag) ->forAll(_| _) => true <_/k> [structural]

// inductive step
rule <k>
val(( BI:BagItem B:Bag)) ->forAll( Var:Id | BEXP:BExp ) => 
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
val(( BI:BagItem B:Bag)) ->exists( Var:Id | BEXP:BExp ) => 
if  BEXP[open(BI)/Var] 
then true 
else val(B) ->exists( Var | BEXP)
endif 
<_/k> 
[structural]

//semantics of Strings
rule Str1:String ++ Str2:String => Str1 +String Str2 [structural]


// semantics of Collection expressions
// rule for empty
rule <k> empty => val(.Bag) <_/k> [structural]


// rules Class .allInstances
rule <k> allInstances(Cls:Id) => val(collectInstanceNames(Cls, INST:Bag)) <_/k>  
       //NB one model only!
       <models>
         <model> <modelName> MN:Id </modelName> // _ leads to ambiguity
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

// when finished, the bag of instances whose AT we are trying to get is empty: 
// take result from temp cell and dissolve
rule <k> (val(.Bag) # AT) => val(B:Bag) <_/k> <temp> B => . </temp> [structural]


// NB all elements in CExp are assumed to have the attribute Id
// may add error rules in the future



// when not finished, the bag of instances whose AT we are trying to get is nonempty
// the value of AT is stored in temp cell
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


rule <k> val(C1) union val(C2)   => val(C1 C2) <_/k> [structural]
rule <k> val(C1) inter val(C2) => val(C1 interBag C2) <_/k> [structural]
rule <k> val(C1) diff val(C2) => val(C1 diffBag C2)  <_/k> [structural]




//collect
// by analogy with forAll, exists
syntax CExp ::=  CExp [ K / Id ] [ditto]
rule <k> val(.Bag) ->collect(_|_) => val(.Bag)  <_/k> [structural]

rule <k>
 val(( BI:BagItem B:Bag)) ->collect( Var:Id | CEXP:CExp ) =>
 CEXP[open(BI)/Var]  union (val(B) ->collect( Var | CEXP))
<_/k> [structural]


//select
// base case: when there is nothing select: take result from temp cell
rule <k>
val(.Bag) ->select(_|_) => val(B) <_/k>
<temp>
 B => .
</temp>
[structural]

syntax K ::= `@temp ( K ) [strict]

//inductive step : place the result in wrapped form at the head of the computation
rule <k>( val(( BI B)) ->select( Var| BEXP:BExp )) => 
@temp(if BEXP[open(BI)/Var] then val(BI) else val(.Bag) endif )
~> (val(B) ->select( Var | BEXP))
<_/k>
[structural]

// and when it's evaluated, place result in temp cell
rule
<k> @temp(val(B))  => . <_/k>
<temp_> 
. => B
<_/temp>
[structural]



// let : just substitution
rule <k> let  X:Id =  CEXP1 in CEXP2  endlet => CEXP2[CEXP1/X] <_/k> [structural]

// if
rule <k> if true then CEXP1:CExp else CEXP2:CExp endif => CEXP1 <_/k> [structural]
rule <k> if false then CEXP1 else CEXP2 endif => CEXP2 <_/k> [structural]

// string stuff

rule val(BagItem(Str1)) ++ Str2 => val(BagItem(Str1 +String Str2)) [structural]
rule Str2 ++ val(BagItem(Str1)) => val(BagItem(Str1 +String Str2)) [structural]
rule val(BagItem(Str1)) ++ val(BagItem(Str2))   =>
      val(BagItem(Str1 +String Str2)) [structural]

endkm

