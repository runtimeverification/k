


kmod CONFIG is including  K + PL-ID

syntax K ::= Id 

syntax Id ::= undefined // to be extended later with class and instance names


  configuration <T>  
                 <oclConstraints> .List </oclConstraints>
                 <models>
                   <model> 
                      <modelName> undefined </modelName>
                      <instance multiplicity = "*">
                         <instName> undefined </instName>
                         <ofClass> undefined </ofClass>
                         <attributes> .Map </attributes>
                      </instance>
                   </model>
                 </models>
                <k color="green"> .K </k> 
                <output> .List</output>
                <mem> .Map </mem>
                <nextLoc> 0 </nextLoc>
                </T>

 
endkm



