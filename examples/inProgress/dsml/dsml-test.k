in dsml.k


kmod CONFORMANCE is including META-MODEL

syntax K ::= checkConf( Id ) |  checkStruct ( Id ) | checkOCL ( Id ) | checkAttr ( Bag ) |  checkLinks ( Bag )




rule
<k> checkConf(Mod:Id) => checkStruct(Mod)~>checkOCL(Mod) <_/k> 


rule <k> checkStruct(Mod) => checkAttr(INST:Bag)~>checkLinks(INST)  <_/k> 
<model> <modelName> Mod </modelName> INST </model> 


rule <k> checkAttr(.Bag) => (.) <_/k> 

rule <k> 
checkAttr((<instance_> <attributes> ATTRINST:Map </attributes> <ofClass> C:Id </ofClass> <_/instance>) REST:Bag)
 => 
consistentAttributes(ATTRINST, ATTRCLS:Map)~>checkAttr(REST) <_/k> 
<class_><className> C</className><declAttributes> ATTRCLS </declAttributes> <_/class>


syntax K ::= consistentAttributes( Map , Map ) |  'ERROR-UNDEFINED-ATTRIBUTE ( Id )

rule consistentAttributes( .Map, M:Map) => . [structural]
rule  consistentAttributes( (attr:Id |->  typedVal(v:Val,T:Type)) M':Map,  ((attr |-> T ) M))=>
consistentAttributes(M',M) [structural]
rule consistentAttributes( (attr |->  typedVal(_,T:Type) M'), .Map) => 'ERROR-UNDEFINED-ATTRIBUTE(attr) 
[structural] 


/*
 syntax Bool  ::= unknownType ( Type , Map ) 

rule unknownType(T, (_ |-> T) _) => false [structural]
rule unknownType(T, ((_ |-> T':Type) M')) => unknownType(T, M') if T' =/= T [structural] --- how to test difference?
rule unknownType(T, .Map) = true [structural] 

*/

 syntax Bag ::= testConfig



syntax Id ::=  'a | 'b | 'A | 'B | 'M | 'Z | 'W | 'attr1 | 'attr2 | 'attr3 | 'Int | 'Bool
syntax Val ::= Int | Bool | String | Id
syntax Type ::= Id 
syntax TypedVal ::= typedVal( Val , Type )
syntax K ::= TypedVal

macro testConfig = 
 <T_>
<metamodel_>
  <classes>
    <class> 
      <className> 'A </className> 
      <extends> object </extends>
      <declAttributes> 'attr1 |-> 'Int </declAttributes >
    </class>
    <class>
      <className> 'B </className> 
     <extends> object </extends>
      <declAttributes> 'attr2 |-> 'Bool </declAttributes >
    <_/class>
  </classes>
<_/metamodel>
<model>
      <modelName> 'M </modelName>
      <instance>
                      <instName>  'a </instName>
                      <ofClass> 'A </ofClass>
                       <attributes> 'attr1 |-> typedVal(1, 'Int) </attributes>
       
       </instance>
       <instance>
                      <instName> 'b </instName>
                       <ofClass> 'B </ofClass>
                       <attributes> 'attr2 |-> typedVal(true, 'Bool) </attributes>
       </instance>
</model>
<k> checkConf('M) </k>
<_/T>


endkm
