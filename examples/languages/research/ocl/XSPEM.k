require meta-model.k
require conformance

module XSPEM is including CONFORMANCE + META-MODEL

syntax #Id ::= "x" | "y" | "run" 

syntax #Id ::= "onexSPEM"
 | "p"
 | "a"
 | "b"
 | "r"
 | "w1"
 | "w2"
 | "process"
 | "activity"
 | "resource"
 | "workSequence"
 | "startedToStart"
 | "startedToFinish"
 | "finishedToStart"
 | "linkToPredecessor"
 | "finishedToFinish"
 | "time"
 | "activities"
 | "tmin"
 | "tmax"
 | "aS"
 | "notStarted"
 | "activityState"
 | "tS"
 | "undef"
 | "timeState"
 | "resources"
 | "resource"
 | "available"
 | "int"
 | "bool"

syntax Bag ::= "initConfig"

macro initConfig = 
<T>
	<oclConstraints>
		OCL(((process.allInstances()).size()) = 1)
		OCL((activity.allInstances())->forAll(x | (((x.linkToPredecessor).size()) >= 1)))
		OCL((activity.allInstances())->forAll(x | (((x.linkToPredecessor).size()) <= 1)))
		.List
	</oclConstraints>
	<instances>
		<instance>
			<instName> p </instName>
			<ofClass> process </ofClass>
			<attributes>
				(time |-> typedElt(0,int))
				(activities |-> typedElt((a::activity),activity))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> a </instName>
			<ofClass> activity </ofClass>
			<attributes>
				(tmin |-> typedElt(5,int))
				(tmax |-> typedElt(8,int))
				(aS |-> typedElt((notStarted::activityState),activityState))
				(tS |-> typedElt((undef::timeState),timeState))
				(resources |-> typedElt((r::resource),resource))
				(time |-> typedElt(0,int))
				(linkToPredecessor |-> typedElt((w2::workSequence), workSequence))
				(activities |-> typedElt((b::activity), activity))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> b </instName>
			<ofClass> activity </ofClass>
			<attributes>
				(tmin |-> typedElt(3,int))
				(tmax |-> typedElt(7,int))
				(aS |-> typedElt((notStarted::activityState),activityState))
				(tS |-> typedElt((undef::timeState),timeState))
				(resources |-> typedElt(.Magma,resource))
				(time |-> typedElt(0, int))
				(activities |-> typedElt(.Magma, activity))
				(linkToPredecessor |-> typedElt((w1::workSequence), workSequence))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> r </instName>
			<ofClass> resource </ofClass>
			<attributes>
				(available |-> typedElt(true,bool))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> w1 </instName>
			<ofClass> workSequence </ofClass>
			<attributes>
				(startedToStart |-> typedElt(.Magma,activity))
				(startedToFinish |-> typedElt(.Magma,activity))
				(finishedToStart |-> typedElt((a::activity),activity))
				(finishedToFinish |-> typedElt(.Magma,activity))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> w2 </instName>
			<ofClass> workSequence </ofClass>
			<attributes>
				(startedToStart |-> typedElt(.Magma,activity))
				(startedToFinish |-> typedElt(.Magma,activity))
				(finishedToStart |-> typedElt(.Magma,activity))
				(finishedToFinish |-> typedElt(.Magma,activity))
				.Map
			</attributes>
		</instance>
	</instances>
// <k>  checkConformance </k>
<k> run </k>
<trace> .List </trace>
<env> .Map </env>
</T>

end module
