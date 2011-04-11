require ../ocl-semantics
require ../conformance

kmod  XSPEM  is including OCL-SEMANTICS + CONFORMANCE

syntax Id ::= x | y 
syntax Id ::= xSPEM
 | activityState
 | notStarted
 | inProgress
 | finished
 | timeState
 | undefined
 | tooEarly
 | ok
 | tooLate
 | process
 | time
 | activities
 | activity
 | tmin
 | tmax
 | aS
 | tS
 | linkToPredecessor
 | resources
 | workSequence
 | startedToStart
 | startedToFinish
 | finishedToStart
 | finishedToFinish
 | resource
 | available

syntax Id ::= onexSPEM
 | p
 | a
 | b
 | r
 | w1
 | w2


syntax Bag ::= initConfig

 macro initConfig = 
<T>
<metamodel>
	<name>
 		xSPEM
	</name>
	<classes>
		<enumeration>
			<enumName>
				activityState
			</enumName>
			BagItem(notStarted) 
			BagItem(inProgress) 
			BagItem(finished) 
		</enumeration>
		<enumeration>
			<enumName>
				timeState
			</enumName>
			BagItem(undefined) 
			BagItem(tooEarly) 
			BagItem(ok) 
			BagItem(tooLate) 
		</enumeration>
		<class>
			<className>
				process
			</className>
			<declAttributes>
				(activities|->activity)
				(time|->int)
				.Map
			</declAttributes>
		</class>
		<class>
			<className>
				activity
			</className>
			<extends>
				BagItem(process) 
			</extends>
			<declAttributes>
				(tmax|->int)
				(linkToPredecessor|->workSequence)
				(resources|->resource)
				(activities|->activity)
				(aS|->activityState)
				(time|->int)
				(tmin|->int)
				(tS|->timeState)
				.Map
			</declAttributes>
		</class>
		<class>
			<className>
				workSequence
			</className>
			<declAttributes>
				(startedToStart|->activity)
				(finishedToStart|->activity)
				(finishedToFinish|->activity)
				(startedToFinish|->activity)
				.Map
			</declAttributes>
		</class>
		<class>
			<className>
				resource
			</className>
			<declAttributes>
				(available|->bool)
				.Map
			</declAttributes>
		</class>
	</classes>
	<oclConstraints>
		OCL(((allInstances(process).size()) = 1))

		OCL(allInstances(activity)->forAll(x |(x#linkToPredecessor).size() >= 1))
		OCL(allInstances(activity)->forAll(x |(x#linkToPredecessor).size() <= 1))
		.List
	</oclConstraints>
</metamodel>
<models>
	<model>
	<modelName> onexSPEM </modelName> 
		<instance>
			<instName> p </instName>
			<ofClass> process </ofClass>
			<attributes>
				(time |->typedElt(val(BagItem(0)),int))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> a </instName>
			<ofClass> activity </ofClass>
			<attributes>
				(tmin |->typedElt(val(BagItem(5)),int))
				(tmax |->typedElt(val(BagItem(8)),int))
				(aS |->typedElt(val(BagItem(notStarted)),activityState))
				(tS |->typedElt(val(BagItem(undefined)),timeState))
				(resources |->typedElt(val(.BagBagItem(r:resource) ),resource))
				(time |->typedElt(val(BagItem(0)),int))
				(linkToPredecessor |->typedElt(val(.BagBagItem(w2:workSequence) ),workSequence))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> b </instName>
			<ofClass> activity </ofClass>
			<attributes>
				(tmin |->typedElt(val(BagItem(5)),int))
				(tmax |->typedElt(val(BagItem(8)),int))
				(aS |->typedElt(val(BagItem(notStarted)),activityState))
				(tS |->typedElt(val(BagItem(undefined)),timeState))
				(resources |->typedElt(val(.BagBagItem(r:resource) ),resource))
				(time |->typedElt(val(BagItem(0)),int))
				(linkToPredecessor |->typedElt(val(.BagBagItem(w1:workSequence) ),workSequence))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> r </instName>
			<ofClass> resource </ofClass>
			<attributes>
				(available |->typedElt(val(BagItem(true)),bool))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> w1 </instName>
			<ofClass> workSequence </ofClass>
			<attributes>
				(startedToStart |->typedElt(val(.Bag),activity))
				(startedToFinish |->typedElt(val(.Bag),activity))
				(finishedToStart |->typedElt(val(.Bag),activity))
				(finishedToFinish |->typedElt(val(.BagBagItem(a:activity) ),activity))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> w2 </instName>
			<ofClass> workSequence </ofClass>
			<attributes>
				(startedToStart |->typedElt(val(.Bag),activity))
				(startedToFinish |->typedElt(val(.Bag),activity))
				(finishedToStart |->typedElt(val(.Bag),activity))
				(finishedToFinish |->typedElt(val(.Bag),activity))
				.Map
			</attributes>
		</instance>
	</model>
</models>
<k>  checkConformance </k>
<output>  .List </output>
<mem>  .Map </mem>
<nextLoc>  0 </nextLoc>
</T>
endkm
