in dsml.k


kmod CONFORMANCE is including META-MODEL

syntax K ::= checkConf( Id ) |  checkStruct ( Id ) | checkOCL ( Id ) | checkAttr ( Bag ) 




rule
<k> checkConf(Mod:Id) => checkStruct(Mod)~>checkOCL(Mod) <_/k> 


rule <k> checkStruct(Mod) => checkAttr(INST:Bag)  <_/k>
     <model> <modelName> Mod </modelName> INST </model> 


rule <k> checkAttr(.Bag) => (.) <_/k> 

rule <k> checkAttr((<instance_> 
                      <attributes> ATTRINST:Map </attributes>
                      <ofClass> C:Id </ofClass> <_/instance>
                   ) REST:Bag)
         =>
         consistentAttributes(ATTRINST, ATTRCLS:Map)~>checkAttr(REST)
     <_/k>
     <class_>
       <className> C</className>
       <declAttributes> ATTRCLS </declAttributes>
     <_/class>


syntax K ::= consistentAttributes( Map , Map ) |  ERROR-UNDEFINED-ATTRIBUTE ( Id )

rule consistentAttributes( .Map, Map:Map) => . [structural]

rule  consistentAttributes( (attr:Id |->  typedVal(v:Val,T:Type)) Map':Map,  
                            ((attr |-> T ) Map))
      =>
      consistentAttributes(Map',Map)
      if isScalar(T)
      [structural]

rule  <k>consistentAttributes( (attr:Id |->  typedVal(v:Val,T:Type)) Map':Map,  
                            ((attr |-> T ) Map))
      =>
      consistentAttributes(Map',Map)
      <_/k>
      <instName> v </instName>
      if isScalar(T) ==Bool false
      [structural]

rule consistentAttributes( (attr |->  typedVal(_,T:Type) Map'), .Map)
     =>
     ERROR-UNDEFINED-ATTRIBUTE(attr) // if unknownType(T, Map)
    [structural] 


/*
 syntax Bool  ::= unknownType ( Type , Map ) 

rule unknownType(T, (_ |-> T) _) => false [structural]
rule unknownType(T, ((_ |-> T':Type) Map')) => unknownType(T, Map') if notBool (T' = T) [structural] // how to test difference?
rule unknownType(T, .Map) = true [structural] 
*/


 syntax Bag ::= testConfig



syntax Id ::=  a | b | `A | `B | `M | `Z | `W | attr1 | attr2 | attr3 
syntax Val ::= Int | Bool | String | Id 
//syntax Type ::= Id 
syntax TypedVal ::= typedVal( Val , Type )
syntax K ::= TypedVal


macro testConfig = 
 <T_>
<metamodel_>
  <classes>
    <class> 
      <className> A </className> 
      <extends> object </extends>
      <declAttributes> attr1 |-> int attr3 |-> B </declAttributes >
    </class>
    <class>
      <className> B </className> 
     <extends> object </extends>
      <declAttributes> attr2 |-> bool </declAttributes >
    <_/class>
  </classes>
<_/metamodel>
<model>
      <modelName> M </modelName>
      <instance>
                      <instName>  a </instName>
                      <ofClass> A </ofClass>
                       <attributes>
                          attr1 |-> typedVal(1, int) 
                          attr3 |-> typedVal(b, B)
                       </attributes>
       
       </instance>
       <instance>
                      <instName> b </instName>
                       <ofClass> B </ofClass>
                       <attributes> attr2 |-> typedVal(true, bool) </attributes>
       </instance>
</model>
<k> checkConf(M) </k>
<_/T>


endkm
