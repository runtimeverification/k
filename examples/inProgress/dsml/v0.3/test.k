require ocl-semantics

kmod TEST is including OCL-SEMANTICS

syntax Id ::=  a | b | modelM | attr1 | attr2 | attr3 | classA | classB | classZ | int | colInt | bool | colBool | colInst



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
               (attr1 |-> typedElt(val(BagItem(a : classA)), colInst))
               (attr3 |-> typedElt(val(BagItem(1)), colInt ))
            </attributes>
          </instance>
          <instance>
            <instName> b </instName>
            <ofClass> classB </ofClass>
            <attributes> 
             (attr2 |-> typedElt(val(BagItem(a : classA) BagItem(a : classA) BagItem(b : classB)), colInst)) </attributes>
          </instance>
       </model> 
     </models> 
        <k>    allInstances(classB) ->select(x | (a : classA) in (x # attr2)  ) </k>
        //<k>    allInstances(classB) ->exists(x | (a : classA) in (x # attr2)  ) </k>
       //<k>    allInstances(classB) ->collect(x | (x # attr2)) </k>
       //<k>    allInstances(classA) ->forAll(x | (x # attr3) = val(BagItem(a : classA))) </k>
       //  <k>     ((a : classA) # attr3) = val(BagItem(a : classA))  </k>
       // <k>      (a : classA) # attr3 = val(BagItem(a : classA)) </k> 
    // <k> let x =  val(BagItem(a : classA)) in (x # attr3) endlet  </k>
     <temp> .Bag </temp>
  </T>

syntax Id ::= x


endkm 