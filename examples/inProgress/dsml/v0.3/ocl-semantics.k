require meta-model
require substitution
kmod OCL-SEMANTICS is including META-MODEL  +  SUBSTITUTION

//PRELIMINARIES
// values

//for instance name of certain class
syntax K ::= Id of Id

// values are either collection values, integers, or Booleans
syntax KResult ::= ValCExp | Int | Bool 



// collection values are  wrapped bags of wrapped ints, bools, or instance names of class name
// the wrappped ints etc use the predefined construction BagItem : K -> BagItem
syntax ValCExp ::=  val ( Bag ) 

// return value of Collection expression

syntax CExp ::= ValCExp



//basic types
syntax Id ::= int | bool | colInt | colBool

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
rule card(.Bag) => 0
rule card(v:BagItem V:Bag) => 1 +Int card(V)


// subset predicate
syntax Bool ::= subset ( Bag , Bag ) 
rule subset(.Bag,  V) => true 
rule subset((v:BagItem V), V':Bag) => if (v  inBag  V') then subset(V,V') else false fi 

// structural 
//SEMANTICS
// semantics of arithmetical expressions
rule A1:Int + A2:Int => A1 +Int A2
rule A1 * A2 => A1 *Int A2
rule A1 / A2 => A1 /Int A2 if notBool (A2 ==Int 0)

rule (- A1) => -Int A1

rule (val(B:Bag) .size()) => card(B)


// semantics of Boolean expressions

rule A1 < A2 => A1 <Int A2
rule A1 <= A2 => A1 <=Int A2
rule A1 > A2 => A1 >Int A2
rule A1 >= A2 => A1 >=Int A2
rule A1 = A2 => A1 ==Int A2 
rule A1 <> A2 => notBool (A1 ==Int A2)

rule B1:Bool and B2:Bool => B1 andBool B2
rule B1 or B2 => B1 orBool B2
rule B1 implies B2 => (notBool B1) orBool B2 
rule B1 equiv B2 => B1 ==Bool B2

rule not B1 => notBool B1

rule isEmpty(val(.Bag)) => true 

rule isEmpty(val(BagIt:BagItem _)) => false 

rule val(C1:Bag) myin val(C2:Bag) => subset(C1,C2)
rule val(C1:Bag) in* val(C2:Bag) => subset(C1,C2) andBool (card(C1) <Int card(C2))
rule val(C1) notin val(C2) => notBool (subset(C1,C2)) 
rule val(C1) notin* val(C2) => notBool (subset(C1,C2) andBool (card(C1) <Int card(C2)))


rule (val(C1) = val(C2)) => C1 ==Bool C2



rule val(.Bag) ->forAll(_| _) => true



rule <k> 
val((BI:BagItem B:Bag)) ->forAll( Var:Id | BEXP:BExp ) =>
kif BEXP[unWrap(BI)/Var] 
then val(B) ->forAll( Var | BEXP)
else false
fik
<_/k> 
[structural]

syntax K ::= unWrap ( BagItem )


rule unWrap(BagItem(kv:K)) => kv [structural]


syntax Bool ::= kif K then BExp else BExp fik

rule 
<k>
kif true  then t:BExp else e:BExp fik => t 
<_/k>  [structural]

rule  
<k>
kif true  then t else e fik => e 
<_/k>
  [structural]
/*

//rule kIf true[KEXP:K  /Var]  then thenBranch:BExp else elseBranch:BExp endkIf => thenBranch
/rule kIf false[KEXP /Var]  then thenBranch else elseBranch endkIf => elseBranch

rule kIf BEXP[KEXP:K  /Var]  then t:BExp else e:BExp endkIf => 


thenBranch
rule kIf false[KEXP /Var]  then thenBranch else elseBranch endkIf => elseBranch


//rule kIf true  then thenBranch:BExp else elseBranch:BExp endkIf => thenBranch
//rule kIf false  then thenBranch else elseBranch endkIf => elseBranch

*/

//semantics for Collection expressions
// rule for empty



rule <k> empty => val(.Bag) <_/k>


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
rule collectInstanceNames(Cls, .Bag) => .Bag 

rule collectInstanceNames(Cls, 
                        (<instance> 
                             <instName> INAME:Id </instName> 
                             <ofClass> Cls </ofClass>
                             <attributes> ATTR:Map </attributes>
                         </instance> 
                        REST:Bag
                       )
                     )
                      =>    BagItem(INAME of Cls)
                      collectInstanceNames(Cls, REST)

rule collectInstanceNames(Cls, 
                        (<instance> 
                             <instName> INAME </instName> 
                             <ofClass> Cls':Id </ofClass>
                             <attributes> ATTR </attributes>
                         </instance> REST:Bag))
                        =>  collectInstanceNames(Cls, REST)
                        if notBool (Cls ==Bool Cls') 


// rule for CExp # Id [strict] 

// when finished, the bag of instances whose AT we are trying to get is empty: 
// take result from temp cell and dissolve
rule <k> (val(.Bag) # AT) => val(B:Bag) <_/k> <temp> B => . </temp> 


// NB all elements in CExp are assumed to have the attribute Id
// may add error rules in the future



// when not finished, the bag of instances whose AT we are trying to get is nonempty
// the value of AT is stored in temp cell
rule <k>  val(BagItem(INAME of Cls) REMAINING:Bag) # AT:Id
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



rule <k> val(C1) union val(C2)   => val(C1 C2) <_/k> 
rule <k> val(C1) inter val(C2) => val(C1 interBag C2) <_/k> 
rule <k> val(C1) diff val(C2) => val(C1 diffBag C2)  <_/k>

// TODO: select, collect, let : need substitution

rule <k> if true then CEXP1:CExp else CEXP2:CExp endif => CEXP1 <_/k> [structural]
rule <k> if false then CEXP1 else CEXP2 endif => CEXP1 <_/k> [structural]

rule <k> let  X:Id =  CEXP1 in CEXP2  endlet => CEXP2[CEXP1/X] <_/k> [structural]

// AUXILIARY DEFINITIONS

 


endkm

