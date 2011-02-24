require ocl-semantics

kmod TEST is including OCL-SEMANTICS

syntax Id ::=  a | b | modelM | attr1 | attr2 | attr3 | classA | classB | classZ | int | colInt | bool | colBool 



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
               (attr1 |-> typedElt(wBag(wInt(1)), int))
               (attr3 |-> typedElt(wBag(wInt(1) wInt(2) wInt(3)), colInt ))
            </attributes>
          </instance>
          <instance>
            <instName> b </instName>
            <ofClass> classB </ofClass>
            <attributes> (attr2 |-> typedElt(wBag(wId(a)), classA)) </attributes>
          </instance>
       </model> 
     </models>
     <k> allInstances(classB) # attr2 </k> 
     <temp> .Bag</temp>
  </T>



endkm 