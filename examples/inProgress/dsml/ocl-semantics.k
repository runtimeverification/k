
require dsml

kmod OCL-VALUES is including OCL-SYNTAX

// values and value sets are the results of evaluating OCL expressions

syntax KResult ::= ValSet 




syntax ValSet ::= .ValSet | Val | ValSet ValSet [assoc comm id: .ValSet]
                | ValSet `Inter ValSet
                | ValSet `Diff ValSet

syntax Val ::= Bool | Int  | instVal ( Bag ) // or better, instVal(BagItem)


rule (v:Val V1:ValSet) Inter (v V2:ValSet) => v (V1 Inter V2) [structural]
rule (v V1) Inter V2 => V1 Inter V2 if notBool (v in V2) [structural]
rule .ValSet Inter V:ValSet => .ValSet [structural]
rule V Inter .ValSet => .ValSet [structural]


rule (v V1) Diff (v V2) => V1 Diff V2 [structural]
rule (v V1) Diff V2 => v (V1 Diff V2) if notBool (v in V2) [structural]
rule .ValSet Diff V:ValSet => .ValSet [structural]
rule V Diff .ValSet => V [structural]


syntax Bool ::= Val in ValSet 
rule v in (v V) => true [structural]
rule v in (v':Val V) => v in V if notBool(v ==Bool v') [structural] 
rule v in .ValSet => false [structural]

endkm

kmod OCL-SEMANTICS is including OCL-VALUES + META-MODEL

// semantics of arithmetical expressions
rule A1:AExp + A2:AExp => A1 +Int A2
rule A1 * A2 => A1 *Int A2
rule A1 / A2 => A1 /Int A2 if A2 =/=Bool 0
rule - A1 => -Int A1 .
//rule (V:ValSet .size()) => card(V)

// semantics of Boolean expressions

rule A1 < A2 => A1 <Int A2
rule A1 <= A2 => A1 <=Int A2
rule A1 > A2 => A1 >Int A2
rule A1 >= A2 => A1 >=Int A2
rule A1 = A2 => A1 ==Int A2 
rule A1 <> A2 => notBool (A1 ==Int A2)
rule B1:BExp and B2:BExp => B1 andBool B2
rule B1 or B2 => B1 orBool B2
rule B1 implies B2 => (notBool B1) orBool B2 
rule B1 equiv B2 => ((notBool B1) orBool B2) andBool ((notBool B2) orBool B1)
rule not B1 => notBool B1
rule C1:CExp in C2:CExp => subset(C1,C2) 
rule C1 in* C2 => subset(C1,C2) andBool (card(C1) <Int card(C2))
rule C1 notin C2 => notBool (subset(C1,C2)) 
rule C1 notin* C2 => notBool (subset(C1,C2) andBool (card(C1) <Int card(C2)))
rule C1 = C2 => subset(C1,C2) andBool subset(C2,C1)
// TODO: forAll, exists - need syntactical substitution


//semantics for Collection expressions

rule empty => .ValSet

rule <k> (C:Class .allInstances) => collectInstances(C,INST:Bag) <_/k> 
<model> <modelName> MOD:Id </modelName>
INST
</model>



syntax TypedName ::= typedName( Id , Class ) // should move to META-MODEL or to CONFORMANCE


//rule <k> (CC:CExp # AT:Attr) => .ValSet <_/k> if CC:CExp ==Bool .ValSet

rule <k> (.ValSet # AT:Attr) => .ValSet <_/k>

/*
rule <k>  (
          instVal(
                   <instance>
                     <instName> BIDON:Id </instName>
                     <ofClass> BIDULE:Class </ofClass>
                     <attributes_> (a:Attr |-> typedName(INSNAME:Id, OFCLASS:Class)) <_/attributes>
                                       // handles synonymous instances in different classes
                  </instance>
                 )
           VV:ValSet
          ) # a
       =>  
          instVal(
                   <instance>
                      <instName> INSNAME </instName>
                      <ofClass> OFCLASS </ofClass> 
                      <attributes> ATR:Map </attributes>
                   </instance>
                  )
          (VV:ValSet # a)
    <_/k>
<model_>
  <instance>
    <instName> INSNAME </instName>
    <ofClass> OFCLASS </ofClass> 
    <attributes> ATR </attributes>
  </instance>
<_/model>

*/

// AUXILIARY DEFINITIONS

//collectInstances function

syntax ValSet ::= collectInstances ( Class , Bag )
rule collectInstances(C, .Bag) => .ValSet
rule collectInstances(C, 
                        (<instance> 
                             <instName> INAME:Id </instName> 
                             <ofClass> C </ofClass>
                             <attributes> ATTR:Map </attributes>
                         </instance> REST:Bag))
                        => 
                         instVal(<instance> 
                             <instName> INAME </instName> 
                             <ofClass> C </ofClass>
                             <attributes> ATTR:Map </attributes>
                         </instance>)
                         collectInstances(C, REST)

// another possibility is that the second case (below) generates an error
rule collectInstances(C, 
                        (<instance> 
                             <instName> INAME </instName> 
                             <ofClass> C':Class </ofClass>
                             <attributes> ATTR:Map </attributes>
                         </instance> REST:Bag))
                        =>  collectInstances(C, REST)
                        if notBool (C ==Bool C') 





// subset predicate
syntax Bool ::= subset ( ValSet , ValSet ) 
rule subset(.ValSet,  V:ValSet) => true 
rule subset((v:Val V), V':ValSet) => if (v in V') then subset(V,V') else false fi //NB Maude's if!

// auxiliary : card predicate
syntax Int ::= card ( ValSet )
rule card(.ValSet) => 0
rule card(v V) => 1 +Int card(V)


endkm