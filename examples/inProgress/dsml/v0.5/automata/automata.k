require ../ocl-semantics
require ../conformance

kmod AUTOMATA is including OCL-SEMANTICS + CONFORMANCE

syntax Id ::= x | y 
syntax Id ::= automata
 | automaton
 | trace
 | active
 | transition
 | label
 | orig
 | dest
 | state
 | in
 | out
 | initialState
 | tr
 | st
 | tr1
 | tr2

syntax Id ::= simple
 | a
 | s0
 | s1
 | t1
 | t2
 | t3


syntax Bag ::= initConfig

 macro initConfig = 
<T>
<metamodel> <name> automata </name>
	<classes>
		<class> <className> automaton </className>
			<declAttributes>
				(trace |-> string)
				(active |-> state)
				 .Map
			</declAttributes>
		</class>
		<class> <className> transition </className>
			<declAttributes>
				(label |-> string)
				(orig |-> state)
				(dest |-> state)
				 .Map
			</declAttributes>
		</class>
		<class> <className> state </className>
			<declAttributes>
				(in |-> transition)
				(out |-> transition)
				 .Map
			</declAttributes>
		</class>
		<class> <className> initialState </className>
			<declAttributes>
				 .Map
			</declAttributes>
		</class>
	</classes>
	<oclConstraints>
		OCL(allInstances(automaton)->forAll(x|(x#active).size() >= 1))
		OCL(allInstances(automaton)->forAll(x|(x#active).size() <= 1))
		OCL(allInstances(transition)->forAll(x|(x#orig).size() >= 1))
		OCL(allInstances(transition)->forAll(x|(x#orig).size() <= 1))
		OCL(allInstances(transition)->forAll(x|(x#orig)->forAll(y|(y#out) includes x)))
		OCL(allInstances(transition)->forAll(x|(x#dest).size() >= 1))
		OCL(allInstances(transition)->forAll(x|(x#dest).size() <= 1))
		OCL(allInstances(transition)->forAll(x|(x#dest)->forAll(y|(y#in) includes x)))
		OCL(allInstances(state)->forAll(x|(x#in)->forAll(y|(y#dest) includes x)))
		OCL(allInstances(state)->forAll(x|(x#out)->forAll(y|(y#orig) includes x)))
		OCL((allInstances(initialState).size() = 1))
		OCL((allInstances(transition)->forAll(tr |not(((tr#label) = "")))))
		OCL((allInstances(state)->forAll(st |(st#out)->forAll(tr1 |(st#out)->forAll(tr2 |(((tr1#label)) = ((tr2#label))) implies (tr1 = tr2))))))
		.List
	</oclConstraints>
</metamodel>
<models>
	<model>
	<modelName> simple </modelName> 
		<instance>
			<instName> a </instName>
			<ofClass> automaton </ofClass>
			<attributes>
				(trace |->typedElt(val(BagItem("")),string))
				(active |->typedElt(val(BagItem(s0:state) ),state))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> s0 </instName>
			<ofClass> state </ofClass>
			<attributes>
				(in |->typedElt(val(BagItem(t1:transition) ),transition))
				(out |->typedElt(val(BagItem(t1:transition) BagItem(t2:transition) ),transition))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> s1 </instName>
			<ofClass> state </ofClass>
			<attributes>
				(in |->typedElt(val(BagItem(t2:transition) BagItem(t3:transition) ),transition))
				(out |->typedElt(val(BagItem(t3:transition) ),transition))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> t1 </instName>
			<ofClass> transition </ofClass>
			<attributes>
				(orig |->typedElt(val(BagItem(s0:state) ),state))
				(dest |->typedElt(val(BagItem(s0:state) ),state))
				(label |->typedElt(val(BagItem("a")),string))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> t2 </instName>
			<ofClass> transition </ofClass>
			<attributes>
				(orig |->typedElt(val(BagItem(s0:state) ),state))
				(dest |->typedElt(val(BagItem(s1:state) ),state))
				(label |->typedElt(val(BagItem("a")),string))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> t3 </instName>
			<ofClass> transition </ofClass>
			<attributes>
				(orig |->typedElt(val(BagItem(s1:state) ),state))
				(dest |->typedElt(val(BagItem(s1:state) ),state))
				(label |->typedElt(val(BagItem("c")),string))
				.Map
			</attributes>
		</instance>
	</model>
</models>
<k>  checkConformance </k>
<mem>  .Map </mem>
<nextLoc>  0 </nextLoc>
</T>
endkm
