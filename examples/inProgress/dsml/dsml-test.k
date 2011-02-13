in dsml.k

kmod META-MODEL-TEST is including META-MODEL
rule [add-instance-name-to-K-cell] : 
    <instance_>
       <instName> objName:Id </instName>
       <checked> false => true </checked> 
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
macro testConfig = 
 <T_>
<model>
      <modelName> object </modelName>
      <instance_>
                      <instName>  'a </instName>
                         <checked> false </checked> 
       <_/instance>
       <instance_>
                      <instName> 'b </instName>
                       <checked> false </checked> 
       <_/instance>
</model>
<_/T>

endkm