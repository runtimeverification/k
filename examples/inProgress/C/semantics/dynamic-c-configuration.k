kmod C-CONFIGURATION is
	including C-SYNTAX
	including COMMON-C-CONFIGURATION
	op nextFile : -> CellLabel
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
							--- maps from Ids
							< env > .Map </ env >
							< types > .Map </ types >
							< structs > .Map </ structs >

							--- information about the block we're in
							< nestingDepth > 0 </ nestingDepth >
							< currentBlock > 0 </ currentBlock >
							< localVariables > .Set </ localVariables > --- used to make sure we don't declare a variable twice in the same scope
							< localAddresses > .Set </ localAddresses > --- used to deallocate memory on leaving a block
						</ local >
						< k > .K </ k >
						
						--- used to figure initializers
						< currentObject > .List </ currentObject >
						< currentSubObject > .List </ currentSubObject >
						< incompleteLength > 0 </ incompleteLength >
						< savedInitialization > .K </ savedInitialization >

						< loopStack > .List </ loopStack >
						< locsWrittenTo > .Bag </ locsWrittenTo >
						--- < holds > .Map </ holds >
						< type * > .K </ type * > --- used for typing expressions
						< declarationTypeHolder > .K </ declarationTypeHolder > --- holds the innermost type while we unroll the type around it
						
						--- general information
						< currentTranslationUnit > "" </ currentTranslationUnit >
						< currentFunction > .K </ currentFunction >
						< currentProgramLoc > .K </ currentProgramLoc >
						
						< calculateGotoMap >
							< gotoCalculation * >
								< computation > .K </ computation >
								< computationTail > .K </ computationTail >
								< declarationStack > .List </ declarationStack >
								< nestingDepth > 0 </ nestingDepth >
								< currentBlock > 0 </ currentBlock >
								< loopStack > .List </ loopStack >
							</ gotoCalculation * >
						</ calculateGotoMap >
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
