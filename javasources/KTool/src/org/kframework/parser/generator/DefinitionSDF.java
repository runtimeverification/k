package org.kframework.parser.generator;

import java.util.List;

import org.kframework.kil.Definition;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.Sort;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.loader.Subsort;
import org.kframework.utils.StringUtil;
import org.kframework.utils.general.GlobalSettings;

public class DefinitionSDF {

	public static String getSdfForPrograms(Definition def) {

		StringBuilder sdf = new StringBuilder("module Integration\n\n");
		sdf.append("imports Common\n");
		sdf.append("imports KTechnique\n");
		sdf.append("imports KBuiltinsBasic\n\n");
		sdf.append("exports\n\n");
		sdf.append("context-free syntax\n");

		DefinitionSDFVisitor psdfv = new DefinitionSDFVisitor();
		CollectTerminalsVisitor terminals = new CollectTerminalsVisitor();
		def.accept(psdfv);
		def.accept(terminals);

		for (Production p1 : psdfv.listProds)
			for (Production p2 : psdfv.listProds)
				if (p1 != p2) {
					String srt1 = ((UserList) p1.getItems().get(0)).getSort();
					String srt2 = ((UserList) p2.getItems().get(0)).getSort();
					if (psdfv.subsorts.contains(new Subsort(srt1, srt2)))
						psdfv.subsorts.add(new Subsort(p1.getSort(), p2.getSort()));
				}

		sdf.append(psdfv.sdf);

		sdf.append("%% subsorts 1\n");
		sdf.append("context-free priorities\n{\n");
		// 1
		// print Sort -> K > A -> B > K -> Sort
		for (Sort s : psdfv.userSorts) {
			if (!s.isBaseSort()) {
				sdf.append("	" + StringUtil.escapeSortName(s.getName()) + " -> K");
				// sdf.append(" {cons(K12" + StringUtil.escapeSortName(s.getSortName()) + ")}";
				sdf.append("\n");
			}
		}
		sdf.append("} > {\n");
		for (Subsort subs : psdfv.subsorts) {
			String s1 = subs.getSmallSort();
			String s2 = subs.getBigSort();
			if (!Sort.isBasesort(s1) && !Sort.isBasesort(s2)) {
				sdf.append("	" + StringUtil.escapeSortName(s1) + " -> " + StringUtil.escapeSortName(s2));
				// sdf.append(" {cons(" + StringUtil.escapeSortName(s2) + "12" + StringUtil.escapeSortName(s1) + ")}";
				sdf.append("\n");
			}
		}
		sdf.append("} > {\n");
		for (Sort s : psdfv.userSorts) {
			if (!s.isBaseSort()) {
				sdf.append("	K -> " + StringUtil.escapeSortName(s.getName()));
				// sdf.append(" {cons(" + StringUtil.escapeSortName(s.getName()) + "12K)}";
				sdf.append("\n");
			}
		}
		sdf.append("}\n\n");

		// TODO: add type warnings option in command line
		if (GlobalSettings.typeWarnings) {
			// 2
			sdf.append("%% subsorts 2\n");
			// print Sort -> K > K -> Sort
			for (Sort s : psdfv.userSorts) {
				if (!s.isBaseSort()) {
					sdf.append("context-free priorities\n{\n");
					sdf.append("        K -> " + StringUtil.escapeSortName(s.getName()));
					// sdf.append(" {cons(" + StringUtil.escapeSortName(s.getSortName()) + "12K)}";
					sdf.append("\n");
					sdf.append("} .> {\n");
					for (Sort ss : psdfv.userSorts) {
						if (!ss.isBaseSort() && DefinitionHelper.isSubsortedEq(s.getName(), ss.getName())) {
							sdf.append("        " + StringUtil.escapeSortName(ss.getName()) + " -> K");
							// sdf.append(" {cons(K12" + StringUtil.escapeSortName(ss.getSortName()) + ")}";
							sdf.append("\n");
						}
					}
					sdf.append("}\n\n");
				}
			}
		} else {
			// 2
			sdf.append("%% subsorts 2\n");
			// print K -> Sort > Sort -> K
			sdf.append("context-free priorities\n{\n");
			for (Sort s : psdfv.userSorts) {
				if (!s.isBaseSort()) {
					sdf.append("	K -> " + StringUtil.escapeSortName(s.getName()));
					// sdf.append(" {cons(" + StringUtil.escapeSortName(s.getSortName()) + "12K)}";
					sdf.append("\n");
				}
			}
			sdf.append("} .> {\n");
			for (Sort s : psdfv.userSorts) {
				if (!s.isBaseSort()) {
					sdf.append("	" + StringUtil.escapeSortName(s.getName()) + " -> K");
					// sdf.append(" {cons(K12" + StringUtil.escapeSortName(s.getSortName()) + ")}";
					sdf.append("\n");
				}
			}
			sdf.append("}\n");
		}

		sdf.append("context-free syntax\n");

		for (Production p : psdfv.outsides) {
			if (p.isListDecl()) {
				UserList si = (UserList) p.getItems().get(0);
				sdf.append("	" + StringUtil.escapeSortName(si.getSort()) + " \"" + si.getSeparator() + "\" " + StringUtil.escapeSortName(p.getSort()) + " -> " + StringUtil.escapeSortName(p.getSort()));
				sdf.append(" {cons(" + p.getAttributes().get("cons") + ")}\n");
				sdf.append("	\"." + p.getSort() + "\" -> " + StringUtil.escapeSortName(p.getSort()));
				sdf.append(" {cons(\"" + StringUtil.escapeSortName(p.getSort()) + "1Empty\")}\n");
			} else if (p.getAttributes().containsKey("bracket")) {
				// don't add bracket attributes added by the user
			} else {
				sdf.append("	");
				List<ProductionItem> items = p.getItems();
				for (int i = 0; i < items.size(); i++) {
					ProductionItem itm = items.get(i);
					if (itm.getType() == ProductionType.TERMINAL) {
						Terminal t = (Terminal) itm;
						if (t.getTerminal().equals(":"))
							sdf.append("DouaPuncteDz ");
						else
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
		for (Sort ss : psdfv.insertSorts)
			sdf.append("	" + StringUtil.escapeSortName(ss.getName()) + " -> InsertDz" + StringUtil.escapeSortName(ss.getName()) + "\n");

		sdf.append("\n\n");
		// print variables, HOLEs
		for (Sort s : psdfv.userSorts) {
			if (!s.isBaseSort()) {
				sdf.append("	VARID  \":\" \"" + s.getName() + "\"        -> VariableDz            {cons(\"" + StringUtil.escapeSortName(s.getName()) + "12Var\")}\n");
			}
		}
		sdf.append("\n");
		for (Sort s : psdfv.userSorts) {
			if (!s.isBaseSort()) {
				sdf.append("	\"HOLE\" \":\" \"" + s.getName() + "\"      -> VariableDz            {cons(\"" + StringUtil.escapeSortName(s.getName()) + "12Hole\")}\n");
			}
		}

		sdf.append("\n");
		sdf.append("	VariableDz -> K\n");

		sdf.append("\n\n");
		sdf.append("	DzDzInt		-> DzInt	{cons(\"DzInt1Const\")}\n");
		sdf.append("	DzDzBool	-> DzBool	{cons(\"DzBool1Const\")}\n");
		sdf.append("	DzDzId		-> DzId		{cons(\"DzId1Const\")}\n");
		sdf.append("	DzDzString	-> DzString	{cons(\"DzString1Const\")}\n");
		sdf.append("	DzDzFloat	-> DzFloat	{cons(\"DzFloat1Const\")}\n");

		sdf.append("\n");
		sdf.append("	DzDzINT		-> DzDzInt\n");
		// sdf.append("	DzDzID		-> DzDzId\n");
		sdf.append("	DzDzBOOL	-> DzDzBool\n");
		sdf.append("	DzDzSTRING	-> DzDzString\n");
		sdf.append("	DzDzFLOAT	-> DzDzFloat\n");
		sdf.append("	\":\" -> DouaPuncteDz {cons(\"DouaPuncte\")}\n");

		sdf.append("\n");

		sdf.append("context-free restrictions\n");
		sdf.append("	VariableDz -/- ~[\\:\\;\\(\\)\\<\\>\\~\\n\\r\\t\\,\\ \\[\\]\\=\\+\\-\\*\\/\\|\\{\\}\\.]\n");
		sdf.append("	DouaPuncteDz -/- [A-Z]\n\n");

		sdf.append("lexical syntax\n");
		for (Production p : psdfv.constants) {
			sdf.append("	" + p.getItems().get(0) + " -> Dz" + StringUtil.escapeSortName(p.getSort()) + "\n");
		}

		sdf.append("\n\n%% sort predicates\n");
		// print is<Sort> predicates (actually KLabel)
		for (Sort s : psdfv.userSorts) {
			sdf.append("	\"is" + s.getName() + "\"      -> DzKLabel\n");
			sdf.append("	\"isSymbolic" + s.getName() + "\"      -> DzKLabel\n");
			sdf.append("	\"sym" + s.getName() + "\"      -> DzKLabel\n");
		}

		sdf.append("\n\n");

		sdf.append("\n%% terminals reject\n");
		for (String t : terminals.terminals) {
			if (t.matches("$?[A-Z][^\\:\\;\\(\\)\\<\\>\\~\\n\\r\\t\\,\\ \\[\\]\\=\\+\\-\\*\\/\\|\\{\\}\\.]*")) {
				sdf.append("	\"" + t + "\" -> VARID {reject}\n");
			}
		}

		sdf.append("\n");
		sdf.append(SDFHelper.getFollowRestrictionsForTerminals(terminals.terminals));

		sdf.append("lexical restrictions\n");
		sdf.append("%% some restrictions to ensure greedy matching for user defined constants\n");
		sdf.append("	DzDzId  -/- [a-zA-Z0-9]\n");
		sdf.append("	DzDzInt -/- [0-9]\n");
		sdf.append("	\"is\" -/- [\\#A-Z]\n");
		sdf.append("\n");

		return sdf.toString();
	}
}
