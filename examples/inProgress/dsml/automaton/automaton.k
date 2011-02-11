in ../dsml.k


kmod META-AUTOMATON is including META-MODEL


  syntax Bag ::= metaAutomaton 

  syntax Id ::= eps
  syntax Id ::= initState | state | automaton | transition
              | label | trace | dest | orig | in | out | name | active

  macro metaAutomaton = 
                 <metamodel>
                   <classes>
                      <class>
                         <className> automaton </className>
                         <extends> object </extends>
                         <declAttributes> 
                             trace : 'List`{K`}
                             active : 'Id
                         </declAttributes>
                      </class>
                      <class>
                         <className> transition </className>
                         <extends> object </extends>
                         <declAttributes> 
                             label : 'String 
                             orig  : 'K
                             dest  : 'K
                         </declAttributes>
                      </class>
                      <class>
                         <className> state </className>
                         <extends> object </extends>
                         <declAttributes>  
                             in  : 'List`{K`}
                             out : 'List`{K`}
                         </declAttributes>
                      </class>
                      <class>
                         <className> initState </className>
                         <extends> state </extends>
                      </class>
                   </classes>
                   <oclConstraints> forAll( t`! : transition | notBool label ==Bool eps)   </oclConstraints>
                 </metamodel>

  rule [one-step-transition] :
       <instance_>
          <ofClass> automaton </ofClass>
          <attributes_>
            trace |-> (Tr:List{K} => Tr,, L:K)
            active |-> (X:K => Y:K)
          <_/attributes>
       <_/instance>
/*
  the below info is redundant for transitions
  if we include description of the both states, then the loop transitions cannot hold
  because the current prototype does not faithfully implement KRAM (?)
       <instance>
          <name> X </name>
          <ofClass> state </ofClass>
          <attributes_>
            out |-> T:K
          <_/attributes>
       </instance> 

       <instance>
          <name> Y:K </name>
          <ofClass> state </ofClass>
          <attributes_>
            in |-> T:K
          <_/attributes>
       </instance> 
*/
       <instance>
          <name> T:K </name>
          <ofClass> transition </ofClass>
          <attributes_>
            label |-> L
            orig |-> X
            dest |-> Y
          <_/attributes>
       </instance> 
endkm


kmod AN-AUTOMATON is including META-AUTOMATON

  syntax Id ::= a | b | s0 | s1 | t1 | t2 | t3 

  syntax Bag ::= anAutomaton

  macro anAutomaton =
  <model>
    <instance> 
      <name> a </name>
      <ofClass> automaton </ofClass>
      <attributes> 
         trace |-> .List{K}
         active |-> s0
      </attributes>
    </instance>
    <instance> 
      <name> s0 </name>
      <ofClass> state </ofClass>
      <attributes> 
         in |-> t1
         out |-> (t1,, t2)
      </attributes>
    </instance>
    <instance> 
      <name> s1 </name>
      <ofClass> state </ofClass>
      <attributes> 
         in |-> (t2,, t3)
         out |-> t3
      </attributes>
    </instance>
    <instance> 
      <name> t1 </name>
      <ofClass> transition </ofClass>
      <attributes> 
         label |-> a
         orig |-> s0
         dest |-> s0
      </attributes>
    </instance>
    <instance> 
      <name> t2 </name>
      <ofClass> transition </ofClass>
      <attributes> 
         label |-> eps
         orig |-> s0
         dest |-> s1
      </attributes>
    </instance>
    <instance> 
      <name> t3 </name>
      <ofClass> transition </ofClass>
      <attributes> 
         label |-> b
         orig |-> s1
         dest |-> s1
      </attributes>
    </instance>
  </model>

endkm

kmod AUTOMATON is including AN-AUTOMATON 
  
  syntax Bag ::= initConfig

  macro initConfig
        =
        <T>
           anAutomaton
        </T>

endkm


