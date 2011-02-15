in dsml.k

kmod META-MODEL-TEST is including META-MODEL
rule [load-instance-name-to-K-cell] : 
    <instance_>
       <instName> objName:Id </instName>
       <checked> false => true </checked> 
    <_/instance> 
  <k_>  . => objName  <_/k>  
  <ccPhase> init </ccPhase>

rule [end-init-phase-when-all-loaded] : 
<model>
(<modelName> n:Id </modelName>)
B:Bag => unCheck(B)
</model>
<ccPhase> init => checkInstances </ccPhase>
if allChecked(B)

syntax Bool ::= allChecked ( Bag ) 

macro allChecked(((<instance_> <checked> false  </checked>  <_/instance>) B)) = false
macro allChecked(((<instance_> <checked> true </checked>  <_/instance>) B)) = allChecked(B)
macro allChecked(.Bag) = true

 syntax Bag ::= unCheck( Bag )

macro unCheck(((<instance> <instName> objName </instName> <checked> b:Bool </checked>  <ofClass> className:Id </ofClass> <attributes> M:Map </attributes></instance>) B)) = 
 (<instance> <instName> objName </instName> <checked> false </checked>  <ofClass> className </ofClass> <attributes>  M </attributes></instance>) unCheck(B)

macro unCheck(.Bag) = .Bag


/*only integer & bool types, and does not take inheritance into account, for now */

syntax Bool ::= consistentAttributes( Map , Map )


macro consistentAttributes( .Map, M:Map) = true
macro consistentAttributes( ((attr:Id |->  _ ) M':Map), .Map) = false
macro consistentAttributes( ((attr |->  i:Int) M'),  ((attr |-> 'Int ) M)) = 
consistentAttributes(M',M)
macro consistentAttributes( ((attr |->  b:Bool) M'),  ((attr |-> 'Bool ) M)) = 
consistentAttributes(M',M)

 

rule [delete-instance-names-with-correct-classes-and-attributes-from-K-cell] :
<class_>
<className> className:Id </className>
<declAttributes> M </declAttributes>
<_/class> 
<instance_>
       <instName> objName </instName>
       <ofClass> className </ofClass> 
       <attributes> M' </attributes>
<_/instance> 
<k_> objName => (.) <_/k>
<ccPhase> checkInstances </ccPhase>
if consistentAttributes(M', M)


rule [goto-next-phase-when-all-instances-classes-OK] :
<ccPhase> checkInstances => checkLinks </ccPhase> 
<k> .K </k>


rule [reload-instance-name-to-K-cell] : 
    <instance_>
       <instName> objName </instName>
       <checked> false => true </checked> 
    <_/instance> 
  <k_>  . => objName  <_/k>  
  <ccPhase> checkLinks </ccPhase>





  syntax Bag ::= testConfig

/*
  macro testConfig =
  <T_>
    <instName> object  </instName>
    <checked> false </checked>
  <_/T>
*/

syntax Id ::=  'a | 'b | 'A | 'B | 'O | 'Z | 'W | 'attr1 | 'attr2 | 'Int | 'Bool
syntax Val ::= Int | Bool 
syntax K ::= Val

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
      <modelName> 'O </modelName>
      <instance>
                      <instName>  'a </instName>
                      <ofClass> 'A </ofClass>
                       <attributes> 'attr1 |-> 1 </attributes>
                      <checked> false </checked> 
       
       </instance>
       <instance>
                      <instName> 'b </instName>
                       <ofClass> 'B </ofClass>
                       <attributes> 'attr2 |-> true </attributes>
                       <checked> false </checked> 
       </instance>
</model>
<_/T>

endkm