require ocl-semantics
require conformance

kmod TEST is including OCL-SEMANTICS + CONFORMANCE

syntax Id ::=  a | b | c | d |  modelM | attr1 | attr2 | attr3 | attr4  | attr5 |  classA | classB | classZ 
| x | y | z | int | bool | string 



syntax Bag ::= testConfig

macro testConfig = 
  <T>
    <metamodel>
      <name> undefined </name> 
      <classes>
        <class> 
          <className> classA </className> 
          <extends> object </extends>
          <declAttributes> attr1 |-> classB attr3 |-> int </declAttributes>
        </class>
        <class>
          <className> classB </className> 
          <extends> object </extends>
          <declAttributes> attr2 |-> classA attr4 |-> string attr5 |-> string  </declAttributes>
        </class>
      </classes>
      <oclConstraints> 
           OCL((empty union 1).size())
           OCL(allInstances(classB)->forAll(x| (x#attr2)->forAll(y|(not (oclType(y) =  classA)  or ((y#attr1) includes x)))))
           OCL( ((allInstances(classB) ->collect(x | ( ((x # attr4)  ++   (x # attr5)) ++ (" only" ++ " if")) ))
                ->collect(y | y ++ " or"))->select(z | z.size()  = 1))
           OCL(empty union ((allInstances(classB) ->collect(x | ( ((x # attr4) ++   (x # attr5)) ++ (" only" ++ " if")))).size()))
           OCL( allInstances(classB) ->select(x |  (x # attr2) includes  (a : classA) ))
           OCL(allInstances(classB)->collect(x | (x # attr2)))
           OCL(allInstances(classA) ->select (x | (x # attr3) < 2) union (b:classB))
           OCL( (b:classA)->select (x | (x # attr3) < 2) union (b:classB))
           OCL( allInstances(classB) ->exists(x | (x # attr2) = (a : classA)))
           OCL(allInstances(classA)->select(x | ((x#attr3) >= 2)))
           OCL(let x =  (a : classA) in (x#attr3) = 1  endlet)
      </oclConstraints> 
    </metamodel>
    <models>
      <model>
        <modelName> modelM </modelName>
          <instance>
            <instName>  a </instName>
            <ofClass>  classA </ofClass>
            <attributes>
               (attr1 |-> typedElt(val(BagItem(c : classB) BagItem(d : classB)), classB))
               (attr3 |-> typedElt(val(BagItem(1)), int ))
            </attributes>
          </instance>
           <instance>
            <instName>  b </instName>
            <ofClass>  classA </ofClass>
            <attributes>
               (attr1 |-> typedElt(val(BagItem(c : classB)), classB))
               (attr3 |-> typedElt(val(BagItem(2)), int ))
            </attributes>
          </instance>
          <instance>
            <instName> c </instName>
            <ofClass> classB </ofClass>
            <attributes> 
             (attr2 |-> typedElt(val(BagItem(a : classA)), classA))
             (attr4 |-> typedElt(val(BagItem("if")), string))
             (attr5 |-> typedElt(val(BagItem(" and")), string))
           </attributes>
          </instance>
        <instance>
            <instName> d </instName>
            <ofClass> classB </ofClass>
            <attributes> 
             (attr2 |-> typedElt(val(BagItem(b : classA)),  classA))
             (attr4 |-> typedElt(val(BagItem("if")), string))
             (attr5 |-> typedElt(val(BagItem(" AND")), string))
           </attributes>
          </instance>
       </model> 
     </models>
 <k> checkConformance </k>
     <mem> .Map </mem>
     <nextLoc> 0 </nextLoc>
  </T>


// send results to output cell, exp/val pairs

endkm 
