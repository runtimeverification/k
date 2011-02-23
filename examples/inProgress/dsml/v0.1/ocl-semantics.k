require meta-model
require substitution
kmod OCL-SEMANTICS is including META-MODEL + OCL-SYNTAX  + SUBSTITUTION



// semantics of arithmetical expressions
rule A1:Int + A2:Int => A1 +Int A2
rule A1 * A2 => A1 *Int A2
rule A1 / A2 => A1 /Int A2 if notBool (A2 ==Int 0)

rule (- A1) => -Int A1

rule (V:KResult .size()) => card(V)

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
//((notBool B1) orBool B2) andBool ((notBool B2) orBool B1)
rule not B1 => notBool B1

rule C1:KResult in C2:KResult => subset(C1,C2) 
rule C1 in* C2 => subset(C1,C2) andBool (card(C1) <Int card(C2))
rule C1 notin C2 => notBool (subset(C1,C2)) 
rule C1 notin* C2 => notBool (subset(C1,C2) andBool (card(C1) <Int card(C2)))
rule C1 = C2 => subset(C1,C2) andBool subset(C2,C1)

// TODO: forAll, exists - need syntactical substitution


//semantics for Collection expressions
// evaluated in K cell only

// rule for empty
rule <k> empty => .KResult <_/k>


// rules Class .allInstances
rule <k> allInstances(C:Class) => collectInstances(C, INST:Bag) <_/k> 
       //NB one model only!
       <models>
         <model> <modelName> MN:Id </modelName> // _ leads to ambiguity
            INST
         </model>
      </models>
 [structural] 
     

//collectInstances function: collects instances of class C
syntax KResult ::= collectInstances ( Class , Bag )
rule collectInstances(C, .Bag) => .KResult

rule collectInstances(C, 
                        (<instance> 
                             <instName> INAME:Id </instName> 
                             <ofClass> C </ofClass>
                             <attributes> ATTR:Map </attributes>
                         </instance> 
                        REST:Bag
                       )
                     )
                      => 
                      instVal(
                               <instance> 
                                <instName> INAME </instName> 
                                <ofClass> C </ofClass>
                                <attributes> ATTR </attributes>
                               </instance>)
                      collectInstances(C, REST)

rule collectInstances(C, 
                        (<instance> 
                             <instName> INAME </instName> 
                             <ofClass> C':Class </ofClass>
                             <attributes> ATTR:Map </attributes>
                         </instance> REST:Bag))
                        =>  collectInstances(C, REST)
                        if notBool (C ==Bool C') 






// rule for CExp # Attr [strict] 
// when finished, take result from temp cell
rule <k> (.KResult # AT:Attr) => VV:KResult <_/k> <temp> VV => .KResult </temp>

// case 1 : the attribute AT is of scalar type
// the value of AT is stored in temp cell
rule <k> (
          instVal(
                   <instance_>
                     <attributes_> AT |-> typedVal(vv:Val, _) <_/attributes>        
                  <_/instance>
                )
                 RESTVAL:KResult)
  # AT
       => RESTVAL  # AT
 <_/k>   
// <temp_> .KResult =>  vv
// <_/temp>




// case 2 : the attribute AT is of type class
// the instance is sought for in the model
// the value of AT is stored in temp cell
rule <k>  (
          instVal(
                   <instance_>
                     <attributes_> AT |-> typedName(INSNAME:Id, OF:Class) <_/attributes>
                                       // handles synonymous instances in different classes
                  <_/instance>
                 )
           VV:KResult
          ) # AT
       =>  VV:KResult # AT
    <_/k>
<model_>
  <instance>
    <instName> INSNAME </instName>
    <ofClass> OF </ofClass> 
    <attributes> ATR:Map </attributes>
  </instance>
<_/model>
<temp_> .KResult =>
          instVal(
                   <instance>
                      <instName> INSNAME </instName>
                      <ofClass> OF </ofClass> 
                      <attributes> ATR </attributes>
                   </instance>
                  )
<_/temp>




// case 3 : the attribute AT is of type collection of instance Ids
// the bag of instances is sought for in the model
rule <k>  (
          instVal(
                   <instance_>
                     <attributes_> AT |-> typedSetOfInstName(ISET:Set{Id}, OFCOL:ClassTypeCol) <_/attributes>
                  <_/instance>
                 )
           VV:KResult
          ) # AT
       =>  VV # AT 
    <_/k>
<model> <modelName> toto:Id </modelName>
ALLINSTANCES:Bag
</model>
<temp_> .KResult =>
         makeInstVal(ISET,ALLINSTANCES)
<_/temp>

syntax KResult ::=  makeInstVal ( Set{Id} , Bag )

rule makeInstVal(ALLNAMES:Set{Id}, .Bag) => .KResult

rule makeInstVal(ALLNAMES,
                  <instance>
                     <instName> INSTNAME:Id </instName> 
                     <ofClass> OFTHECLASS:Class </ofClass>
                     <attributes> ATR </attributes>
                  </instance> REMAINING:Bag) 
    => if isIn(INSTNAME,ALLNAMES)
       then
                  instVal( <instance>
                     <instName> INSTNAME </instName> 
                     <ofClass> OFTHECLASS:Class </ofClass>
                     <attributes> ATR </attributes>
                  </instance> ) 
                  makeInstVal(ALLNAMES,REMAINING)
       else

         makeInstVal(ALLNAMES,REMAINING)

       fi

syntax Bool ::= isIn ( Id , Set{Id} )
rule isIn (XX:Id , (XX , NAMES:Set{Id}) ) => true [structural]
 rule isIn (XX, (XX':Id ,  NAMES)) => isIn(XX,  NAMES) if notBool (XX ==Bool XX') [structural]
rule isIn (XX, .Set{Id}) => false [structural]




// case 4 : the attribute AT is of type collection of  values

rule <k>  (
          instVal(
                   <instance_>
                     <attributes_> AT |-> typedSetOfVal(VVV:KResult, _) <_/attributes>
                  <_/instance>
                 )
           VV
          ) # AT
       =>  VV # AT 
    <_/k>
<temp_> .KResult =>
         VVV
<_/temp>


rule <k> C1 union C2   => C1 C2 <_/k> 
rule <k> C1 inter C2 => C1 Inter C2 <_/k> 
rule <k> C1 diff C2 => C1 Diff C2  <_/k>

// TODO: select, collect, let : need substitution

rule <k> if true then C1 else C2 endif => C1 <_/k>
rule <k> if false then C1 else C2 endif => C2 <_/k>

// rule <k> let  X:Var =  C1  inn C2  endlet => C2[C1/X] <_/k>

// AUXILIARY DEFINITIONS

 



// subset predicate
syntax Bool ::= subset ( KResult , KResult ) 
rule subset(.KResult,  V:KResult) => true 
rule subset((v:Val V), V':KResult) => if (v  inValSet  V') then subset(V,V') else false fi //NB Maude's if!

// auxiliary : card predicate
syntax Int ::= card ( KResult )
rule card(.KResult) => 0
rule card(v V) => 1 +Int card(V)


endkm

