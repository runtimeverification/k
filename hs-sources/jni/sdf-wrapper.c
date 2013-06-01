#include "sglr.h"
#include "MEPT-posinfo.h"
#include "MEPT-implode.h"
#include "MEPT-flatten.h"
#include "parse-table.h"
#include<stdio.h>

ATbool set_global_options(void)
{
	SG_FILTER_ON();
	SG_FILTER_DIRECTEAGERNESS_ON();
	SG_FILTER_EAGERNESS_ON();
	SG_FILTER_INJECTIONCOUNT_ON();
	SG_FILTER_PRIORITY_ON();
	SG_FILTER_REJECT_ON();
	SG_STARTSYMBOL_ON();
	SG_OUTPUT_ON();
	//                 SG_ASFIX2ME_ON();
	SG_BINARY_ON();

	return ATtrue;
} 


void init() {
	printf("Initializing...");
	fflush(stdout);
	ATerm bottomOfStack;
	char  *ATlibArgv[] = { "sdf-wrapper",
		"-at-silent",   /* Choose sensible options here */
		"-at-afuntable", "15",
		"-at-termtable", "18"
	};

	ATinit(6, ATlibArgv, &bottomOfStack);
	PT_initMEPTApi();
	LOC_initLocationApi();
	PT_initAsFix2Api(); 
	initErrorApi(); 
	set_global_options();
	printf("done.\n");
	fflush(stdout);
}

ATerm implode(PT_ParseTree tree) {
	ATbool interpret_cons = ATtrue;
	ATbool remove_layout = ATtrue;
	ATbool remove_literals = ATtrue;
	ATbool remove_injections = ATtrue;
	ATbool remove_parsetree = ATtrue;
	ATbool implode_lexicals = ATtrue;
	ATbool keep_annotations =ATtrue;
	ATbool interpret_alt = ATtrue;
	ATbool interpret_seq = ATtrue;
	ATbool interpret_opt = ATtrue;
	ATbool interpret_layout_place_holder=ATfalse;

	return (ATerm) PT_implodeParseTree(tree,
			interpret_cons ,
			remove_layout ,
			remove_literals ,
			remove_injections ,
			remove_parsetree ,
			implode_lexicals ,
			keep_annotations,
			interpret_alt ,
			interpret_seq ,
			interpret_opt ,
			interpret_layout_place_holder);
}

char* parse(const char* parse_table_name, 
		const char* input, 
		const char* start_symbol,
		const char* input_file_name, int* size) {
	printf("Looking up parse table...");
	fflush(stdout);
	
	language lang_name = ATmake("<str>", parse_table_name);
	char** err;
	if (!SG_LookupParseTable(lang_name,parse_table_name)) {
		printf("not found.  Loading parse table...");
		fflush(stdout);
		if(ATmatch(SGopenLanguage(lang_name, 
						parse_table_name, 
						parse_table_name),
					"snd-value(open-language-failed(<str>,<str>))", 
					&err, 
					NULL)) {
			ATfprintf(stderr,
					"could not open %s as a parse table\n", err);
			return NULL;
		} 
	}
	printf("done.\n");
	fflush(stdout);
	printf("Parsing...");
	fflush(stdout);
	ATerm parse_tree = SGparseStringWithLoadedTable(parse_table_name,
			lang_name, input, start_symbol, input_file_name);

	if (!parse_tree) printf("\tError parsing\n");
	printf("done.\n");
	fflush(stdout);
	printf("Adding position info...");
	fflush(stdout);
	PT_ParseTree parseTree =  PT_ParseTreeFromTerm(parse_tree);

	parseTree = PT_addParseTreePosInfoSome(input_file_name, parseTree, -1, 
			ATfalse, ATfalse);
	if (!parseTree) printf("\tError adding Position Info\n");
	printf("done.\n");
	fflush(stdout);
	printf("Imploding...");
	fflush(stdout);
	parse_tree = implode(parseTree);
	printf("done.\n");
	if (!parse_tree) printf("\tError imploding\n");
	fflush(stdout);

	printf("Output to string...");
	fflush(stdout);
	char* output = ATwriteToBinaryString(parse_tree, size);
//	char* output = ATwriteToSharedString(parse_tree, &size);
//	char* output = ATwriteToString(parse_tree);
//	printf("Output size: %d\n", size);
	printf("Output : %s\n", output);
	printf("done.\n");
	fflush(stdout);

	return output;
} 
