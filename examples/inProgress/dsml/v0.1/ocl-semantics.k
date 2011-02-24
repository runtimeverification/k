require meta-model
require substitution
kmod OCL-SEMANTICS is including META-MODEL  +  SUBSTITUTION

//PRELIMINARIES
// a few structural rule about sets of values
syntax Bag ::= Bag `Inter Bag

rule  (v:BagItem V1:Bag) Inter (v:BagItem V2:Bag) => v (V1 Inter V2) [structural]
rule (v V1) Inter V2 =>  V1 Inter V2 if notBool (v  inBag  V2) [structural]
rule .Bag Inter V:Bag => .Bag [structural]
rule V Inter .Bag => .Bag [structural]


syntax Bag ::= Bag `Diff Bag
rule (v V1) Diff (v V2) => V1 Diff V2 [structural]
rule (v V1) Diff V2 => v (V1 Diff V2) if notBool (v  inBag  V2) [structural]
rule .Bag Diff V:Bag => .Bag [structural]
rule V Diff .Bag => V [structural]


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


//SEMANTICS
// semantics of arithmetical expressions
rule A1:Int + A2:Int => A1 +Int A2
rule A1 * A2 => A1 *Int A2
rule A1 / A2 => A1 /Int A2 if notBool (A2 ==Int 0)

rule (- A1) => -Int A1

rule (wBag(B:Bag) .size()) => card(B)


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

rule wBag(C1:Bag) in wBag(C2:Bag) => subset(C1,C2) 
rule wBag(C1) in* wBag(C2) => subset(C1,C2) andBool (card(C1) <Int card(C2))
rule wBag(C1) notin wBag(C2) => notBool (subset(C1,C2)) 
rule wBag(C1) notin* wBag(C2) => notBool (subset(C1,C2) andBool (card(C1) <Int card(C2)))

// no rule necessary for equality because it is trivial 
//rule wBag(C1) = wBag(C2) => C1 ==Bool C2

// TODO: forAll, exists - need syntactical substitution


//semantics for Collection expressions
// rule for empty

rule <k> empty => wBag(.Bag) <_/k>


// rules Class .allInstances
rule <k> allInstances(Cls:Id) => wBag(collectInstances(Cls, INST:Bag)) <_/k>  
       //NB one model only!
       <models>
         <model> <modelName> MN:Id </modelName> // _ leads to ambiguity
            INST
         </model>
      </models>
 [structural] 
     

//collectInstances function: collects instances of class Cls
syntax Bag ::= collectInstances ( Id , Bag ) 
rule collectInstances(Cls, .Bag) => .Bag 

rule collectInstances(Cls, 
                        (<instance> 
                             <instName> INAME:Id </instName> 
                             <ofClass> Cls </ofClass>
                             <attributes> ATTR:Map </attributes>
                         </instance> 
                        REST:Bag
                       )
                     )
                      =>   <instance> 
                               <instName> INAME </instName> 
                               <ofClass> Cls </ofClass>
                               <attributes> ATTR </attributes>
                            </instance>
                      collectInstances(Cls, REST)

rule collectInstances(Cls, 
                        (<instance> 
                             <instName> INAME </instName> 
                             <ofClass> Cls':Id </ofClass>
                             <attributes> ATTR </attributes>
                         </instance> REST:Bag))
                        =>  collectInstances(Cls, REST)
                        if notBool (Cls ==Bool Cls') 






// rule for CExp # Id [strict] 
// when finished, take result from temp cell

rule <k> . => wBag(B:Bag) </k> <temp> B => . </temp>


// case 1 : the attribute AT is a bag of values 
// the value of AT is stored in temp cell
rule <k>  wBag(  <instance_>
                     <attributes_> AT:Id |-> typedElt(wBag(B), T:Id) <_/attributes>        
                  <_/instance>
              ) # AT
       => .
 <_/k>   
 <temp_> .Bag =>  B
 <_/temp>
if isBasic(T)


syntax Bool ::= isBasic( Id )

rule isBasic(T) =>
 (T ==Bool int) orBool   // may need to add Strings, enumerated types depending on given MM
   (T ==Bool colInt) orBool 
   (T ==Bool bool) orBool 
    (T ==Bool colBool) [structural]

// case 2 : the attribute AT is a bag of instance names
// the instances are sought for in the model 
// the value of the instance's AT is stored in temp cell

rule <k>  wBag(  <instance_>
                     <attributes_> AT |-> typedElt(wBag(B), T) <_/attributes>
                  <_/instance>        
           ) # AT
       =>  .
    <_/k>
<models> // 1 model only!
<model> <modelName> toto:Id </modelName>
ALLINSTANCES:Bag
</model>
</models>
<temp_> .Bag =>
         getInstancesByName(B,ALLINSTANCES)
<_/temp>
if notBool isBasic(T)


syntax Bag ::=  getInstancesByName ( Bag , Bag )

rule getInstancesByName(NAMES:Bag, .Bag) => .Bag

rule getInstancesByName(NAMES,
                  (<instance>
                     <instName> INSTNAME:Id </instName> 
                     <ofClass> Cls </ofClass>
                     <attributes> AT </attributes>
                  </instance> REMAINING:Bag))
    => if (wId(INSTNAME) inBag NAMES)
       then
                   <instance>
                     <instName> INSTNAME </instName> 
                     <ofClass> Cls </ofClass> 
                     <attributes> AT </attributes>
                  </instance> 
                  getInstancesByName(NAMES,REMAINING)
       else

         getInstancesByName(NAMES,REMAINING)

       fi



/*

rule <k> C1 union C2   => C1 C2 <_/k> 
rule <k> C1 inter C2 => C1 Inter C2 <_/k> 
rule <k> C1 diff C2 => C1 Diff C2  <_/k>

// TODO: select, collect, let : need substitution

rule <k> if true then C1 else C2 endif => C1 <_/k>
rule <k> if false then C1 else C2 endif => C2 <_/k>

 rule <k> let  X:Id =  C1  inn C2  endlet => C2[C1/X] <_/k>

// AUXILIARY DEFINITIONS

 



// auxiliary : card predicate


*/

endkm

