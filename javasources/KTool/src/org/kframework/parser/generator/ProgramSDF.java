package org.kframework.parser.generator;

import org.kframework.kil.*;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.utils.StringUtil;

import java.util.List;

/**
 * Collect the syntax module, call the syntax collector and print SDF for programs.
 * 
 * @author RaduFmse
 * 
 */
public class ProgramSDF {

	public static String getSdfForPrograms(Definition def) {

		// collect all the syntax modules
		CollectSynModulesVisitor csmv = new CollectSynModulesVisitor();
		def.accept(csmv);

		// collect the syntax from those modules
		ProgramSDFVisitor psdfv = new ProgramSDFVisitor();
		CollectTerminalsVisitor ctv = new CollectTerminalsVisitor();
		for (String modName : csmv.synModNames) {
			Module m = def.getModulesMap().get(modName);
			m.accept(psdfv);
			m.accept(ctv);
		}

		StringBuilder sdf = new StringBuilder();
		sdf.append("module Program\n\n");
		sdf.append("imports Common\n");
		sdf.append("imports KBuiltinsBasic\n");
		sdf.append("exports\n\n");
		sdf.append("context-free syntax\n");
		sdf.append(psdfv.sdf);

		sdf.append("context-free start-symbols\n");
		sdf.append("\n%% start symbols\n	");

		for (String s : psdfv.startSorts) {
			if (!s.equals("Start"))
				sdf.append(StringUtil.escapeSortName(s) + " ");
		}

		sdf.append("K\n");
		sdf.append("context-free syntax\n");

		for (Production p : psdfv.outsides) {
			if (p.isListDecl()) {
				UserList si = (UserList) p.getItems().get(0);
				sdf.append("	{" + StringUtil.escapeSortName(si.getSort()) + " \"" + si.getSeparator() + "\"}* -> " + StringUtil.escapeSortName(p.getSort()));
				sdf.append(" {cons(\"" + p.getAttributes().get("cons") + "\")}\n");
			} else {
				sdf.append("	");
				List<ProductionItem> items = p.getItems();
				for (int i = 0; i < items.size(); i++) {
					ProductionItem itm = items.get(i);
					if (itm.getType() == ProductionType.TERMINAL) {
						Terminal t = (Terminal) itm;
						sdf.append("\"" + t.getTerminal() + "\" ");
					} else if (itm.getType() == ProductionType.SORT) {
						Sort srt = (Sort) itm;
						sdf.append(StringUtil.escapeSortName(srt.getName()) + " ");
					}
				}
				sdf.append("-> " + StringUtil.escapeSortName(p.getSort()));
				sdf.append(SDFHelper.getSDFAttributes(p.getAttributes()) + "\n");
			}
		}

		for (String ss : psdfv.sorts)
			sdf.append("	" + StringUtil.escapeSortName(ss) + " -> InsertDz" + StringUtil.escapeSortName(ss) + "\n");

		sdf.append("\n\n");
		sdf.append("	DzDzInt		-> DzInt	{cons(\"DzInt1Const\")}\n");
		sdf.append("	DzDzBool	-> DzBool	{cons(\"DzBool1Const\")}\n");
		sdf.append("	DzDzId		-> DzId		{cons(\"DzId1Const\")}\n");
		sdf.append("	DzDzString	-> DzString	{cons(\"DzString1Const\")}\n");
		sdf.append("	DzDzFloat	-> DzFloat	{cons(\"DzFloat1Const\")}\n");

		sdf.append("\n");
		sdf.append("	DzDzINT		-> DzDzInt\n");
		sdf.append("	DzDzID		-> DzDzId\n");
		sdf.append("	DzDzBOOL	-> DzDzBool\n");
		sdf.append("	DzDzSTRING	-> DzDzString\n");
		sdf.append("	DzDzFLOAT	-> DzDzFloat\n");
		sdf.append("\n");

		sdf.append("\n%% start symbols subsorts\n");
		for (String s : psdfv.startSorts) {
			if (!Sort.isBasesort(s) && !DefinitionHelper.isListSort(s))
				sdf.append("	" + StringUtil.escapeSortName(s) + "		-> K\n");
		}

		sdf.append("lexical syntax\n");
		for (Production prd : psdfv.constants) {
			sdf.append("	" + prd.getItems().get(0) + " -> Dz" + StringUtil.escapeSortName(prd.getSort()) + "\n");
		}

		sdf.append("\n\n");

		for (String t : ctv.terminals) {
			if (t.matches("[a-zA-Z][a-zA-Z0-9]*")) {
				sdf.append("	\"" + t + "\" -> DzDzID {reject}\n");
			}
		}

		sdf.append("\n");
		sdf.append(SDFHelper.getFollowRestrictionsForTerminals(ctv.terminals));

		sdf.append("\n");

		return sdf.toString();
	}
}
