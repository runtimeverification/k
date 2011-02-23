require ocl-semantics

kmod TEST is including OCL-SEMANTICS

syntax Id ::=  a | b | modelM 

syntax Attr ::=  attr1 | attr2 | attr3 

syntax Class ::=  classA | classB | classZ

syntax K ::= Attr | Class

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
          <declAttributes> attr1 |-> int attr3 |-> colInt </declAttributes>
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
               (attr3 |-> typedSetOfVal( (1), colInt ))
            </attributes>
          </instance>
          <instance>
            <instName> b </instName>
            <ofClass> classB </ofClass>
            <attributes> (attr2 |-> typedName(a, classA)) </attributes>
          </instance>
       </model> 
     </models>
     <k> allInstances(classA) # attr1 </k> 
     <temp> .KResult </temp>
  </T>


/*
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
       </model>
     </models>
     <k> allInstances(classA) </k> 
     <temp> .ValSet </temp>
  </T>

*/
endkm 