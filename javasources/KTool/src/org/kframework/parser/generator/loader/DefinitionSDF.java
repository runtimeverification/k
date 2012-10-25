package org.kframework.parser.generator.loader;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.kframework.kil.Attributes;
import org.kframework.kil.Definition;
import org.kframework.kil.PriorityBlock;
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

	@SuppressWarnings("unused")
	public static String getSdfForPrograms(Definition def) {

		String sdf = "module Integration\n\n";
		sdf += "imports Common\n";
		sdf += "imports KTechnique\n";
		sdf += "imports KBuiltinsBasic\n\n";
		sdf += "exports\n\n";
		sdf += "context-free syntax\n";

/*		Set<Sort> sorts = new HashSet<Sort>(); // list of inserted sorts that need to avoid the priority filter

		DefinitionSDFVisitor psdfv = new DefinitionSDFVisitor();
		CollectTerminalsVisitor terminals = new CollectTerminalsVisitor();
		def.accept(psdfv);
		def.accept(terminals);

		{
			if (psdfv.prilist.size() > 0) {
				// if (psdfv.prilist.size() <= 1 && syn.getPriorities().get(0).getBlockAssoc() == null) {
				// // weird bug in SDF - if you declare only one production in a priority block, it gives parse errors
				// // you need to have at least 2 productions or a block association
				// PriorityBlock prt = psdfv.prilist.get(0);
				// for (Production p : prt.getProductions())
				// psdfv.outsides.add(p);
				// } else
				{
					sdf += "context-free priorities\n";

					for (PriorityBlock prt : psdfv.prilist) {
						if (prt.getAssoc() == null)
							sdf += "{\n";
						else
							sdf += "{ " + prt.getAssoc() + ":\n";
						for (Production p : prt.getProductions()) {
							sdf += "	";
							List<ProductionItem> items = p.getItems();
							for (int i = 0; i < items.size(); i++) {
								ProductionItem itm = items.get(i);
								if (itm.getType() == ProductionType.TERMINAL) {
									Terminal t = (Terminal) itm;
									if (t.getTerminal().equals(":"))
										sdf += "DouaPuncteDz ";
									else
										sdf += "\"" + t.getTerminal() + "\" ";
								} else if (itm.getType() == ProductionType.SORT) {
									Sort srt = (Sort) itm;
									// if we are on the first or last place and this sort is not a list, just print the sort
									if (i == 0 || i == items.size() - 1) {
										sdf += StringUtil.escapeSortName(srt.getName()) + " ";
									} else {
										// if this sort should be inserted to avoid the priority filter, then add it to the list
										sorts.add(srt);
										sdf += "InsertDz" + StringUtil.escapeSortName(srt.getName()) + " ";
									}
								}
							}
							sdf += "-> " + StringUtil.escapeSortName(p.getSort());
							sdf += getSDFAttributes(p.getAttributes()) + "\n";
						}
						sdf += "} > ";
					}
					sdf = sdf.substring(0, sdf.length() - 3) + "\n\n";
				}
			}
		}

		sdf += "%% subsorts 1\n";
		sdf += "context-free priorities\n{\n";
		// 1
		// print Sort -> K > A -> B > K -> Sort
		for (Sort s : psdfv.userSorts) {
			if (!s.isBaseSort()) {
				sdf += "	" + StringUtil.escapeSortName(s.getName()) + " -> K";
				// sdf += " {cons(\"K12" + StringUtil.escapeSortName(s.getSortName()) + "\")}";
				sdf += "\n";
			}
		}
		sdf += "} > {\n";
		for (Subsort subs : psdfv.subsorts) {
			String s1 = subs.getSmallSort();
			String s2 = subs.getBigSort();
			if (!Sort.isBasesort(s1) && !Sort.isBasesort(s2)) {
				sdf += "	" + StringUtil.escapeSortName(s1) + " -> " + StringUtil.escapeSortName(s2);
				// sdf += " {cons(\"" + StringUtil.escapeSortName(s2) + "12" + StringUtil.escapeSortName(s1) + "\")}";
				sdf += "\n";
			}
		}
		sdf += "} > {\n";
		for (Sort s : psdfv.userSorts) {
			if (!s.isBaseSort()) {
				sdf += "	K -> " + StringUtil.escapeSortName(s.getName());
				// sdf += " {cons(\"" + StringUtil.escapeSortName(s.getName()) + "12K\")}";
				sdf += "\n";
			}
		}
		sdf += "}\n\n";

		// TODO: add type warnings option in command line
		if (GlobalSettings.typeWarnings) {
			// 2
			sdf += "%% subsorts 2\n";
			// print Sort -> K > K -> Sort
			for (Sort s : psdfv.userSorts) {
				if (!s.isBaseSort()) {
					sdf += "context-free priorities\n{\n";
					sdf += "        K -> " + StringUtil.escapeSortName(s.getName());
					// sdf += " {cons(\"" + StringUtil.escapeSortName(s.getSortName()) + "12K\")}";
					sdf += "\n";
					sdf += "} .> {\n";
					for (Sort ss : psdfv.userSorts) {
						if (!ss.isBaseSort() && DefinitionHelper.isSubsortedEq(s.getName(), ss.getName())) {
							sdf += "        " + StringUtil.escapeSortName(ss.getName()) + " -> K";
							// sdf += " {cons(\"K12" + StringUtil.escapeSortName(ss.getSortName()) + "\")}";
							sdf += "\n";
						}
					}
					sdf += "}\n\n";
				}
			}
		} else {
			// 2
			sdf += "%% subsorts 2\n";
			// print K -> Sort > Sort -> K
			sdf += "context-free priorities\n{\n";
			for (Sort s : psdfv.userSorts) {
				if (!s.isBaseSort()) {
					sdf += "	K -> " + StringUtil.escapeSortName(s.getName());
					// sdf += " {cons(\"" + StringUtil.escapeSortName(s.getSortName()) + "12K\")}";
					sdf += "\n";
				}
			}
			sdf += "} .> {\n";
			for (Sort s : psdfv.userSorts) {
				if (!s.isBaseSort()) {
					sdf += "	" + StringUtil.escapeSortName(s.getName()) + " -> K";
					// sdf += " {cons(\"K12" + StringUtil.escapeSortName(s.getSortName()) + "\")}";
					sdf += "\n";
				}
			}
			sdf += "}\n";
		}

		sdf += "context-free syntax\n";

		for (Production p : psdfv.outsides) {
			if (p.isListDecl()) {
				UserList si = (UserList) p.getItems().get(0);
				sdf += "	" + StringUtil.escapeSortName(si.getSort()) + " \"" + si.getSeparator() + "\" " + StringUtil.escapeSortName(p.getSort()) + " -> " + StringUtil.escapeSortName(p.getSort());
				sdf += " {cons(\"" + p.getAttributes().get("cons") + "\")}\n";
				sdf += "	\"." + p.getSort() + "\" -> " + StringUtil.escapeSortName(p.getSort());
				sdf += " {cons(\"" + StringUtil.escapeSortName(p.getSort()) + "1Empty\")}\n";
			} else if (p.getAttributes().containsKey("bracket")) {
				// don't add bracket attributes added by the user
			} else {
				sdf += "	";
				List<ProductionItem> items = p.getItems();
				for (int i = 0; i < items.size(); i++) {
					ProductionItem itm = items.get(i);
					if (itm.getType() == ProductionType.TERMINAL) {
						Terminal t = (Terminal) itm;
						if (t.getTerminal().equals(":"))
							sdf += "DouaPuncteDz ";
						else
							sdf += "\"" + t.getTerminal() + "\" ";
					} else if (itm.getType() == ProductionType.SORT) {
						Sort srt = (Sort) itm;
						sdf += StringUtil.escapeSortName(srt.getName()) + " ";
					}
				}
				sdf += "-> " + StringUtil.escapeSortName(p.getSort());
				sdf += getSDFAttributes(p.getAttributes()) + "\n";
			}
		}
		for (Sort ss : sorts)
			sdf += "	" + StringUtil.escapeSortName(ss.getName()) + " -> InsertDz" + StringUtil.escapeSortName(ss.getName()) + "\n";

		sdf += "\n\n";
		// print variables, HOLEs
		for (Sort s : psdfv.userSorts) {
			if (!s.isBaseSort()) {
				sdf += "	VARID  \":\" \"" + s.getName() + "\"        -> VariableDz            {cons(\"" + StringUtil.escapeSortName(s.getName()) + "12Var\")}\n";
			}
		}
		sdf += "\n";
		for (Sort s : psdfv.userSorts) {
			if (!s.isBaseSort()) {
				sdf += "	\"HOLE\" \":\" \"" + s.getName() + "\"      -> VariableDz            {cons(\"" + StringUtil.escapeSortName(s.getName()) + "12Hole\")}\n";
			}
		}

		sdf += "\n";
		sdf += "	VariableDz -> K\n";

		sdf += "\n\n";
		sdf += "	DzDzInt		-> DzInt	{cons(\"DzInt1Const\")}\n";
		sdf += "	DzDzBool	-> DzBool	{cons(\"DzBool1Const\")}\n";
		sdf += "	DzDzId		-> DzId		{cons(\"DzId1Const\")}\n";
		sdf += "	DzDzString	-> DzString	{cons(\"DzString1Const\")}\n";
		sdf += "	DzDzFloat	-> DzFloat	{cons(\"DzFloat1Const\")}\n";

		sdf += "\n";
		sdf += "	DzDzINT		-> DzDzInt\n";
		// sdf += "	DzDzID		-> DzDzId\n";
		sdf += "	DzDzBOOL	-> DzDzBool\n";
		sdf += "	DzDzSTRING	-> DzDzString\n";
		sdf += "	DzDzFLOAT	-> DzDzFloat\n";
		sdf += "	\":\" -> DouaPuncteDz {cons(\"DouaPuncte\")}\n";

		sdf += "\n";

		sdf += "context-free restrictions\n";
		sdf += "	VariableDz -/- ~[\\:\\;\\(\\)\\<\\>\\~\\n\\r\\t\\,\\ \\[\\]\\=\\+\\-\\*\\/\\|\\{\\}\\.]\n";
		sdf += "	DouaPuncteDz -/- [A-Z]\n\n";

		sdf += "lexical syntax\n";
		for (Production p : psdfv.constants) {
			sdf += "	\"" + p.getItems().get(0) + "\" -> Dz" + StringUtil.escapeSortName(p.getSort()) + "\n";
		}

		sdf += "\n\n%% sort predicates\n";
		// print is<Sort> predicates (actually KLabel)
		for (Sort s : psdfv.userSorts) {
			sdf += "	\"is" + s.getName() + "\"      -> DzKLabel\n";
		}

		sdf += "\n\n";

		sdf += "\n%% terminals reject\n";
		for (String t : terminals.defterminals) {
			if (t.matches("$?[A-Z][^\\:\\;\\(\\)\\<\\>\\~\\n\\r\\t\\,\\ \\[\\]\\=\\+\\-\\*\\/\\|\\{\\}\\.]*")) {
				sdf += "	\"" + t + "\" -> VARID {reject}\n";
			}
		}

		sdf += "\n";
		sdf += getFollowRestrictionsForTerminals(false);

		sdf += "lexical restrictions\n";
		sdf += "%% some restrictions to ensure greedy matching for user defined constants\n";
		sdf += "	DzDzId  -/- [a-zA-Z0-9]\n";
		sdf += "	DzDzInt -/- [0-9]\n";
		sdf += "	\"is\" -/- [\\#A-Z]\n";
*/
		return sdf + "\n";
	}

	private static String getSDFAttributes(Attributes attrs) {
		String str = " {";

		if (attrs.containsKey("prefer"))
			str += "prefer, ";
		if (attrs.containsKey("avoid"))
			str += "avoid, ";
		if (attrs.containsKey("left"))
			str += "left, ";
		if (attrs.containsKey("right"))
			str += "right, ";
		if (attrs.containsKey("non-assoc"))
			str += "non-assoc, ";
		if (attrs.containsKey("bracket"))
			str += "bracket, ";
		if (attrs.containsKey("cons"))
			str += "cons(\"" + attrs.get("cons") + "\"), ";

		if (str.endsWith(", "))
			return str.substring(0, str.length() - 2) + "}";
		else
			return "";
	}
}
