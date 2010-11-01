mod C-CONFIGURATION is
	including C-SYNTAX .
	including COMMON-C-CONFIGURATION .
	---including PL-BUILTINS .

	op Task : -> CellLabel .
	op todo : -> CellLabel .
	op fresh : -> CellLabel .
	op exchangable : -> CellLabel .
	op gmem : -> CellLabel .
	
	mb configuration 
		--- < T > 
			--- < Task * >
				--- < exchangable >
					--- < k > .K </ k >
					--- < env > .Map </ env > 
					--- < mem > .Map </ mem > 
					--- < malloced > .Map </ malloced >	
					--- < output > "" </ output >					
					--- < form > .K </ form >
				--- </ exchangable >
				--- < types > .Map </ types >
				--- < loopStack > .List </ loopStack >
			--- </ Task * >
			--- < statics > .Map </ statics >
			--- < todo > .K </ todo >
			--- < nextLoc > 1 </ nextLoc >
			--- < fresh > 1 </ fresh >
			--- < genv > .Map </ genv >
			--- < typedefs > .Map </ typedefs >
		--- </ T > 
		< T >
			< Task * >
				< k > P:Program </ k >
				< env > .Map </ env >
				< loopStack > .List </ loopStack >
				< locals > .Bag </ locals >
				< parameters > .Bag </ parameters >
				< types > .Map </ types >
				< output > "" </ output >
				< malloced > .Map </ malloced >
				< mem > .Map </ mem >
				< statics > .Map </ statics >
				---< form > TrueFormula </ form >
			</ Task * >
			< todo > .K </ todo >
			< typedefs > .Map </ typedefs >
			< callStack > .List </ callStack >
			< nextLoc > 0 </ nextLoc >
			< genv > .Map </ genv > 
			< gmem > .Map </ gmem > 
		</ T >
		: KSentence .
	
endm
