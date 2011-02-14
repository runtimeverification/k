in dsml.k

kmod META-MODEL-TEST is including META-MODEL
rule [add-instance-name-to-K-cell] : 
    <class>
               <className> className:Id </className>
    <_/class>
    <instance_>
       <instName> objName:Id </instName>
       <checked> false => true </checked> 
       <ofClass> className <_/ofClass>
    <_/instance> 
  <k_>  . => objName  <_/k>  


  syntax Bag ::= testConfig

/*
  macro testConfig =
  <T_>
    <instName> object  </instName>
    <checked> false </checked>
  <_/T>
*/

syntax Id ::=  'a | 'b | 'A | 'B | 'O | 'Z

macro testConfig = 
 <T_>
<metamodel_>
  <classes_>
   <class>
    <className> 'A </className> 
   <_/class>
   <class>
    <className> 'B </className> 
   <_/class>
  <_/classes>
<_/metamodel>
<model>
      <modelName> 'O </modelName>
      <instance_>
                      <instName>  'a </instName>
                      <ofClass> 'A </ofClass>
                      <checked> false </checked> 
       
       <_/instance>
       <instance_>
                      <instName> 'b </instName>
                       <ofClass> 'B </ofClass>
                       <checked> false </checked> 
       <_/instance>
</model>
<_/T>

endkm