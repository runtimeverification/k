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
			< currentTranslationUnit > "" </ currentTranslationUnit >
			< programText > .Map </ programText >
			< threads >
				< thread * >
					< callStack > .List </ callStack >
					< control >
						< local > 
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
