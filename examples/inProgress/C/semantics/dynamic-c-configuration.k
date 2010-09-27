kmod C-CONFIGURATION is
	including C-SYNTAX
	including COMMON-C-CONFIGURATION

	configuration 
		< T > 
			< gotoMap > .Map </ gotoMap >
			< genv > .Map </ genv >
			< gtypes > .Map </ gtypes >
			< gstructs > .Map </ gstructs >
			< mem > .Map </ mem >
			< nextLoc > 0 </ nextLoc >
			< freshNat > 0 </ freshNat >
			< nextFile > 0 </ nextFile >
			< malloced > .Map </ malloced >
			< statics > .Map </ statics >
			< sizes > .Map </ sizes >
			< openFiles > .Map </ openFiles >
			< busy > .Bag </ busy >
			< programText > .Map </ programText >
			< externalDefinitions > .Map </ externalDefinitions >
			< internalDefinitions > .Map </ internalDefinitions >
			< declarations > .Set </ declarations >
			< preLinkage > .Map </ preLinkage >
			< preTypes > .Map </ preTypes >
			< translationUnits > .Bag </ translationUnits >
			< functionTranslationUnits > .Map </ functionTranslationUnits >
			< declarationOrder > .Map </ declarationOrder >
			< messages > .List </ messages >
			--- < linkage > .Map </ linkage >
			< threads >
				< thread * >
					< callStack > .List </ callStack >
					< control >
						< local >
							< nestingDepth > 0 </ nestingDepth >
							< currentBlock > 0 </ currentBlock >
							< structs > .Map </ structs >
							< env > .Map </ env >
							< types > .Map </ types >
							< currentObject > .List </ currentObject >
							< currentSubObject > .List </ currentSubObject >
							< incompleteLength > 0 </ incompleteLength >
							< savedInitialization > .K </ savedInitialization >
							< initMaxes > .Map </ initMaxes >
						</ local >
						< k > .K </ k >
						< currentTranslationUnit > "" </ currentTranslationUnit >
						--- < typeSimplifier *> 
							--- < specifier > .Bag </ specifier >
							--- < storage > .Bag </ storage >
							--- < modifier > .Bag </ modifier >
						--- </ typeSimplifier *>
						< locsWrittenTo > .Bag </ locsWrittenTo >
						< holds > .Map </ holds >
						< currentFunction > .K </ currentFunction >
						< currentProgramLoc > .K </ currentProgramLoc >
						< type * > .K </ type * >
						< loopStack > .List </ loopStack >
						< blockStack > .List </ blockStack >
						< locals > .Bag </ locals >
						< declarationTypeHolder > .K </ declarationTypeHolder >
					</ control >
				</ thread * >
			</ threads >
			< unfinishedComputation > .K </ unfinishedComputation >
		</ T >
		< files > .Map </ files > --- filenames to strings
		< input > "" </ input >
		< output > "" </ output >
		< resultValue > .K </ resultValue >

endkm
