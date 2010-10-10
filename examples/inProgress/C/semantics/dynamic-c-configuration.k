kmod C-CONFIGURATION is
	including C-SYNTAX
	including COMMON-C-CONFIGURATION

	configuration 
		< T > 
			--- < gotoMap > .Map </ gotoMap >
			< genv > .Map </ genv >
			< gtypes > .Map </ gtypes >
			< gstructs > .Map </ gstructs >
			< mem > .Map </ mem >
			< nextLoc > 0 </ nextLoc >
			< freshNat > 0 </ freshNat >
			--- < nextFile > 0 </ nextFile >
			< malloced > .Map </ malloced >
			< statics > .Map </ statics >
			< internalLocations > .Map </ internalLocations >
			< externalLocations > .Map </ externalLocations >
			--- < sizes > .Map </ sizes >
			< openFiles > .Map </ openFiles >
			--- < busy > .Bag </ busy >
			< programText > .Map </ programText >
			< externalDefinitions > .Map </ externalDefinitions >
			< internalDefinitions > .Map </ internalDefinitions >
			< declarations > .Set </ declarations >
			< preLinkage > .Map </ preLinkage >
			< preTypes > .Map </ preTypes >
			< translationUnits > .Bag </ translationUnits >
			< functionTranslationUnits > .Map </ functionTranslationUnits >
			< declarationOrder > .Map </ declarationOrder >
			--- < messages > .List </ messages >
			< threads >
				< thread * >
					< callStack > .List </ callStack > --- stack of "control" cells
					< control >
						< blockStack > .List </ blockStack > --- stack of "local" cells
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
							< localVariables > .Set </ localVariables >
							< localAddresses > .Set </ localAddresses >
						</ local >
						< k > .K </ k >
						< currentTranslationUnit > "" </ currentTranslationUnit >
						< locsWrittenTo > .Bag </ locsWrittenTo >
						--- < holds > .Map </ holds >
						< currentFunction > .K </ currentFunction >
						< currentProgramLoc > .K </ currentProgramLoc >
						< type * > .K </ type * >
						< loopStack > .List </ loopStack >
						< declarationTypeHolder > .K </ declarationTypeHolder >
						--- < allLocalAddresses > .Set </ allLocalAddresses >
					</ control >
				</ thread * >
			</ threads >
			< unfinishedComputation > .K </ unfinishedComputation > --- this is here to make it easy to check if we've terminated.  it disappears when we terminate
		</ T >
		< files > .Map </ files > --- filenames to strings
		< input > "" </ input >
		< output > "" </ output >
		< resultValue > .K </ resultValue >

endkm
