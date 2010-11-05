Build the tool:
	- run "make dist"  in the main C directory

	
Changes to the CABS abstract syntax tree:
	- Different cases and names (e.g., "Signed" instead of "Tsigned", "DecDef" instead of "DECDEF", etc.)
	- "Identifier" around strings
	- Flattened SpecifierElem
	- Wrap statements with StatementLoc holding the location
	PROTO => Prototype
	NO_INIT => NoInit
