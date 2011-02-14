in dsml.k

kmod META-MODEL-TEST is including META-MODEL
rule [add-instance-name-to-K-cell] : 
    <class>
               <className> className:Id </className>
    <_/class>
    <instance_>
       <instName> objName:Id </instName>
       <checked> false => true </checked> 
       <ofClass> className </ofClass>
    <_/instance> 
  <k_>  . => objName  <_/k>  
  <ccPhase> init </ccPhase>



rule [do-something-else-when-all-checked] : 
<model>
(<modelName> n:Id </modelName>)
B:Bag => unCheck(B)
</model>
/* <k_>  . => 'done  <_/k> */
<ccPhase> init => loaded </ccPhase>
if allChecked(B)



 syntax Bool ::= allChecked ( Bag ) 

macro allChecked(((<instance_> <checked> false  </checked>  <_/instance>) B)) = false
macro allChecked(((<instance_> <checked> true </checked>  <_/instance>) B)) = allChecked(B)
macro allChecked(.Bag) = true

 syntax Bag ::= unCheck( Bag )



macro unCheck(((<instance> <instName> objName </instName> <checked> b:Bool </checked>  <ofClass> className </ofClass> <attributes> .Map </attributes></instance>) B)) = 
 (<instance> <instName> objName </instName> <checked> false </checked>  <ofClass> className </ofClass> <attributes> .Map </attributes></instance>) unCheck(B)


/*
macro unCheck(((<instance_> BB:Bag <checked> b:Bool </checked>  <_/instance>) B)) = 
 (<instance_> BB <checked> false </checked> <_/instance>) unCheck(B)
*/
macro unCheck(.Bag) = .Bag


  syntax Bag ::= testConfig

/*
  macro testConfig =
  <T_>
    <instName> object  </instName>
    <checked> false </checked>
  <_/T>
*/

syntax Id ::=  'a | 'b | 'A | 'B | 'O | 'Z | 'done

macro testConfig = 
 <T_>
<metamodel_>
  <classes>
    <class> /* strange : if I put the classses in <classes_> <_/classes>, class 'A disappears */
      <className> 'A </className> 
    <_/class>
    <class>
      <className> 'B </className> 
    <_/class>
  </classes>
<_/metamodel>
<model>
      <modelName> 'O </modelName>
      <instance_>
                      <instName>  'a </instName>
                      <ofClass> 'B </ofClass>
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