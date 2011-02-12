Build the tool:
	- run "make"  in the main C directory

Interpret a program:
	- dist/kcc program.c
	- ./a.out
	
	Take a look at 'kcc -h' for some options.
	
(Some of the) Changes to the CABS abstract syntax tree:
	- Different cases and names (e.g., "Signed" instead of "Tsigned", "DecDef" instead of "DECDEF", etc.)
	- "Identifier" around strings
	- Flattened SpecifierElem
	- Wrap statements with StatementLoc holding the location
	PROTO => Prototype
	NO_INIT => NoInit
