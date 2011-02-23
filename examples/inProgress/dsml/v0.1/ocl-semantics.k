require dsml
 // require substitution
kmod OCL-SEMANTICS is including META-MODEL + OCL-SYNTAX  // + SUBSTITUTION

// sets of identifiers
syntax Set{Id}  ::= Id | .Set{Id} 
                     | Set{Id} , Set{Id} [assoc comm id: .Set{Id}  hybrid] 

// the various kinds of attributes in instances
syntax K ::= typedVal ( Val , ScalarType ) | typedName ( Id , Class ) | 
             typedSetOfInstName ( Set{Id} , ClassTypeCol ) | typedSetOfVal ( ValSet , ScalarTypeCol )


rule (v:Val V1:ValSet) Inter (v V2:ValSet) => v (V1 Inter V2) [structural]
rule (v V1) Inter V2 => V1 Inter V2 if notBool (v  inValSet  V2) [structural]
rule .ValSet Inter V:ValSet => .ValSet [structural]
rule V Inter .ValSet => .ValSet [structural]


rule (v V1) Diff (v V2) => V1 Diff V2 [structural]
rule (v V1) Diff V2 => v (V1 Diff V2) if notBool (v  inValSet  V2) [structural]
rule .ValSet Diff V:ValSet => .ValSet [structural]
rule V Diff .ValSet => V [structural]


syntax Bool ::= Val  inValSet  ValSet 
rule v  inValSet  (v V) => true [structural]
rule v  inValSet  (v':Val V) => v  inValSet  V if notBool(v ==Bool v') [structural] 
rule v  inValSet  .ValSet => false [structural]



// semantics of arithmetical expressions
rule A1:Int + A2:Int => A1 +Int A2
rule A1 * A2 => A1 *Int A2
rule A1 / A2 => A1 /Int A2 if notBool (A2 ==Int 0)

rule (- A1) => -Int A1

rule (V:ValSet .size()) => card(V)

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

rule C1:ValSet in C2:ValSet => subset(C1,C2) 
rule C1 in* C2 => subset(C1,C2) andBool (card(C1) <Int card(C2))
rule C1 notin C2 => notBool (subset(C1,C2)) 
rule C1 notin* C2 => notBool (subset(C1,C2) andBool (card(C1) <Int card(C2)))
rule C1 = C2 => subset(C1,C2) andBool subset(C2,C1)

// TODO: forAll, exists - need syntactical substitution


//semantics for Collection expressions
// evaluated in K cell only

// rule for empty
rule <k> empty => .ValSet <_/k>


// rules Class .allInstances
rule <k> (C:Class .allInstances) => collectInstances(C,INST:Bag) <_/k> 
         <model> <modelName> MN:Id </modelName> // _ leads to ambiguity
            INST:Bag
         </model> [structural] 

//collectInstances function: collects instances of class C


syntax ValSet ::= collectInstances ( Class , Bag )
rule collectInstances(C:Class, .Bag) => .ValSet

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
rule <k> (.ValSet # AT:Attr) => VV:ValSet <_/k> <temp> VV => .ValSet </temp>

// case 1 : the attribute AT is of scalar type
// the value of AT is stored in temp cell
rule <k> (
          instVal(
                   <instance>
                     <instName> BIDON:Id </instName>
                     <ofClass> BIDULE:Class </ofClass>
                     <attributes_> AT|-> typedVal(vv:Val, TT:ScalarType)<_/attributes>        
                  </instance>
                )
                 RESTVAL:ValSet)  # AT
       =>  RESTVAL  # AT
 <_/k>   
<temp_> .ValSet =>  vv
<_/temp>




// case 2 : the attribute AT is of type class
// the instance is sought for in the model
// the value of AT is stored in temp cell
rule <k>  (
          instVal(
                   <instance>
                     <instName> BIDON:Id </instName>
                     <ofClass> BIDULE:Class </ofClass>
                     <attributes_> AT|-> typedName(INSNAME:Id, OF:Class) <_/attributes>
                                       // handles synonymous instances in different classes
                  </instance>
                 )
           VV:ValSet
          ) # AT
       =>  VV:ValSet # AT
    <_/k>
<model_>
  <instance>
    <instName> INSNAME </instName>
    <ofClass> OF </ofClass> 
    <attributes> ATR:Map </attributes>
  </instance>
<_/model>
<temp_> .ValSet =>
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
                   <instance>
                     <instName> BIDON:Id </instName>
                     <ofClass> BIDULE:Class </ofClass>
                     <attributes_> AT|-> typedSetOfInstName(ISET:Set{Id}, OFCOL:ClassTypeCol) <_/attributes>
                  </instance>
                 )
           VV:ValSet
          ) # AT
       =>  VV:ValSet # AT 
    <_/k>
<model> <modelName> toto:Id </modelName>
ALLINSTANCES:Bag
</model>
<temp_> .ValSet =>
         makeInstVal(ISET,ALLINSTANCES)
<_/temp>

syntax ValSet ::=  makeInstVal ( Set{Id} , Bag )

rule makeInstVal(ALLNAMES:Set{Id}, .Bag) => .ValSet 

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

/*
rule makeInstVal(ALLNAMES,  
                  <instance>
                     <instName> INSTNAME':Id </instName> 
                     <ofClass> OFTHECLASS:Class </ofClass>
                     <attributes> ATR </attributes>
                  </instance> REMAINING:Bag) 
    =>
    makeInstVal(ALLNAMES,REMAINING)
    if notBool isPresent(INSTNAME',ALLNAMES)
*/

syntax Bool ::= isIn ( Id , Set{Id} )
rule isIn (XX:Id , (XX , NAMES:Set{Id}) ) => true [structural]
 rule isIn (XX, (XX':Id ,  NAMES)) => isIn(XX,  NAMES) if notBool (XX ==Bool XX') [structural]
rule isIn (XX, .Set{Id}) => false [structural]




// case 4 : the attribute AT is of type collection of  values

rule <k>  (
          instVal(
                   <instance_>
                     <attributes_> AT|-> typedSetOfVal(VVV:ValSet, _) <_/attributes>
                  <_/instance>
                 )
           VV:ValSet
          ) # AT
       =>  VV:ValSet # AT 
    <_/k>
//<temp> .K =>
//         VVV
//<_/temp>


rule <k> C1 union C2   => C1 C2 <_/k> 
rule <k> C1 inter C2 => C1 Inter C2 <_/k> 
rule <k> C1 diff C2 => C1 Diff C2  <_/k>

// TODO: select, collect, let : need substitution

rule <k> if true then C1 else C2 endif => C1 <_/k>
rule <k> if false then C1 else C2 endif => C2 <_/k>

// rule <k> let  X:Var =  C1  inn C2  endlet => C2[C1/X] <_/k>

// AUXILIARY DEFINITIONS





// subset predicate
syntax Bool ::= subset ( ValSet , ValSet ) 
rule subset(.ValSet,  V:ValSet) => true 
rule subset((v:Val V), V':ValSet) => if (v  inValSet  V') then subset(V,V') else false fi //NB Maude's if!

// auxiliary : card predicate
syntax Int ::= card ( ValSet )
rule card(.ValSet) => 0
rule card(v V) => 1 +Int card(V)


endkm

kmod TEST is including OCL-SEMANTICS

syntax Id ::=  a | b | modelM 

syntax Attr ::=  attr1 | attr2 | attr3 

syntax Class ::=  classA | classB | classZ

/*
syntax Id ::= a | b | `M
syntax Class ::= `A | `B | `Z


*/


syntax Bag ::= testConfig

macro testConfig = 
  <T>
    <metamodel>
      <name> undefined </name> 
      <classes>
        <class> 
          <className> classA </className> 
          <extends> object </extends>
          <declAttributes> attr1 |-> int attr3 |-> col(int) </declAttributes>
        </class>
        <class>
          <className> classB </className> 
          <extends> object </extends>
          <declAttributes> attr2 |-> classA </declAttributes>
        </class>
      </classes>
      <oclConstraints> .List </oclConstraints> 
    </metamodel>
    <models>
      <model>
        <modelName> modelM </modelName>
          <instance>
            <instName>  a </instName>
            <ofClass>  classA </ofClass>
            <attributes>
               (attr1 |-> typedVal(1, int))
               (attr3 |-> typedSetOfVal( (1 2 3), col(int) ))
            </attributes>
          </instance>
          <instance>
            <instName> b </instName>
            <ofClass> classB </ofClass>
            <attributes> (attr2 |-> typedName(a, classA)) </attributes>
          </instance>
       </model> 
     </models>
     <k> ((classA .allInstances)) # attr3 </k> 
     <temp> .K </temp>
  </T>


endkm 