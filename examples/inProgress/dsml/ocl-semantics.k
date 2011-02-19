require dsml

kmod OCL-VALUES is including OCL-SYNTAX
// merge with OCL semantics
// the results of evaluating OCL expressions

syntax KResult ::= ValSet 
syntax CExp ::= ValSet 
syntax AExp ::= Int
syntax BExp ::= Bool



syntax ValSet ::= .ValSet | Val | ValSet ValSet [hybrid gather(E e) comm id: .ValSet]
                | ValSet `Inter ValSet
                | ValSet `Diff ValSet

syntax Val ::= Bool | Int  | instVal ( Bag ) // or better, instVal(BagItem)



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

endkm



kmod OCL-SEMANTICS is including OCL-VALUES + META-MODEL // + SUBSTITUTION


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

rule <k> empty => .ValSet <_/k>

rule <k> (C:Class .allInstances) => collectInstances(C,INST:Bag) <_/k> 
         <model> <modelName> MN:Id </modelName> // _ leads to ambiguity
            INST
         </model>

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


syntax K ::= typedName( Id , Class ) // should move to META-MODEL or to CONFORMANCE


rule <k> (.ValSet # AT:Attr) => .ValSet <_/k>

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
                      <instName> INSNAME:Id </instName>
                      <ofClass> OFCLASS:Id </ofClass> 
                      <attributes> ATR:Map </attributes>
                   </instance>
                  )
 //         (VV:ValSet # a) //problematic!!!!
// celula mem
    <_/k>
<model_>
  <instance>
    <instName> INSNAME </instName>
    <ofClass> OFCLASS </ofClass> 
    <attributes> ATR </attributes>
  </instance>
<_/model>


rule <k> C1 union C2   => C1 C2 <_/k> 
rule <k> C1 inter C2 => C1 Inter C2 <_/k> 
rule <k> C1 diff C2 => C1 Diff C2  <_/k>

// TODO: select, collect, let : need substitution

rule <k> if true then C1 else C2 endif => C1 <_/k>
rule <k> if false then C1 else C2 endif => C2 <_/k>

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

