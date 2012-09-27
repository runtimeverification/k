package org.kframework.parser.generator.loader;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sort;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.parser.generator.basic.Item;
import org.kframework.parser.generator.basic.ModuleItem;
import org.kframework.parser.generator.basic.Priority;
import org.kframework.parser.generator.basic.Sentence;
import org.kframework.parser.generator.basic.Subsort;
import org.kframework.parser.generator.basic.Syntax;
import org.kframework.parser.generator.basic.Item.ItemType;
import org.kframework.parser.generator.basic.ModuleItem.ModuleType;
import org.kframework.parser.generator.basic.Sentence.SentenceType;
import org.kframework.utils.Error;
import org.kframework.utils.StringUtil;
import org.kframework.utils.general.GlobalSettings;

public class DefinitionSDF {

	public static String getSdfForPrograms(Definition def) {

		String sdf = "module Integration\n\n";
		sdf += "imports Common\n";
		sdf += "imports KTechnique\n";
		sdf += "imports KBuiltinsBasic\n\n";
		sdf += "exports\n\n";
		sdf += "context-free syntax\n";

		Set<Sort> sorts = new HashSet<Sort>(); // list of inserted sorts that need to avoid the priority filter

		
		DefinitionSDFVisitor psdfv = new DefinitionSDFVisitor();
		def.accept(psdfv);
/*
		{
			if (psdfv.prilist.size() > 0) {
				if (prilist.size() <= 1 && syn.getPriorities().get(0).getBlockAssoc() == null) {
					// weird bug in SDF - if you declare only one production in a priority block, it gives parse errors
					// you need to have at least 2 productions or a block association
					Priority prt = prilist.get(0);
					for (Production p : prt.getProductions())
						outsides.add(p);
				} else {
					sdf += "context-free priorities\n";

					for (Priority prt : prilist) {
						if (prt.getBlockAssoc() == null)
							sdf += "{\n";
						else
							sdf += "{ " + prt.getBlockAssoc() + ":\n";
						for (Production p : prt.getProductions()) {
							sdf += "	";
							List<Item> items = p.getItems();
							for (int i = 0; i < items.size(); i++) {
								Item itm = items.get(i);
								if (itm.getType() == ItemType.TERMINAL) {
									Terminal t = (Terminal) itm;
									if (t.getTerminal().equals(":"))
										sdf += "DouaPuncteDz ";
									else
										sdf += "\"" + t.getTerminal() + "\" ";
								} else if (itm.getType() == ItemType.SORT) {
									Sort srt = (Sort) itm;
									// if we are on the first or last place and this sort is not a list, just print the sort
									if (i == 0 || i == items.size() - 1) {
										sdf += StringUtil.escapeSortName(srt.getSortName()) + " ";
									} else {
										// if this sort should be inserted to avoid the priority filter, then add it to the list
										sorts.add(srt);
										sdf += "InsertDz" + StringUtil.escapeSortName(srt.getSortName()) + " ";
									}
								}
							}
							sdf += "-> " + StringUtil.escapeSortName(p.getProdSort().getSortName());
							sdf += getSDFAttributes(p.getAttributes()) + "\n";
						}
						sdf += "} > ";
					}
					sdf = sdf.substring(0, sdf.length() - 3) + "\n\n";
				}
			}
		}

		Set<Subsort> sbs = getSubsorts();
		for (Production p1 : listProds)
			for (Production p2 : listProds)
				if (p1 != p2) {
					Sort srt1 = ((UserList) p1.getItems().get(0)).getSort();
					Sort srt2 = ((UserList) p2.getItems().get(0)).getSort();
					if (sbs.contains(new Subsort(srt1, srt2)))
						subsorts.add(new Subsort(p1.getProdSort(), p2.getProdSort()));
				}

		sdf += "%% subsorts 1\n";
		sdf += "context-free priorities\n{\n";
		// 1
		// print Sort -> K > A -> B > K -> Sort
		for (Sort s : userSorts) {
			if (!s.isBaseSort()) {
				sdf += "	" + StringUtil.escapeSortName(s.getSortName()) + " -> K";
				// sdf += " {cons(\"K12" + StringUtil.escapeSortName(s.getSortName()) + "\")}";
				sdf += "\n";
			}
		}
		sdf += "} > {\n";
		for (Subsort subs : subsorts) {
			Sort s1 = (Sort) subs.getSmallSort();
			Sort s2 = subs.getBigSort();
			if (!s1.isBaseSort() && !s2.isBaseSort()) {
				sdf += "	" + StringUtil.escapeSortName(s1.getSortName()) + " -> " + StringUtil.escapeSortName(s2.getSortName());
				// sdf += " {cons(\"" + StringUtil.escapeSortName(s2.getSortName()) + "12" + StringUtil.escapeSortName(s1.getSortName()) + "\")}";
				sdf += "\n";
			}
		}
		sdf += "} > {\n";
		for (Sort s : userSorts) {
			if (!s.isBaseSort()) {
				sdf += "	K -> " + StringUtil.escapeSortName(s.getSortName());
				// sdf += " {cons(\"" + StringUtil.escapeSortName(s.getSortName()) + "12K\")}";
				sdf += "\n";
			}
		}
		sdf += "}\n\n";

		// TODO: add type warnings option in command line
		if (GlobalSettings.typeWarnings) {
			// 2
			sdf += "%% subsorts 2\n";
			// print Sort -> K > K -> Sort
			for (Sort s : userSorts) {
				if (!s.isBaseSort()) {
					sdf += "context-free priorities\n{\n";
					sdf += "        K -> " + StringUtil.escapeSortName(s.getSortName());
					// sdf += " {cons(\"" + StringUtil.escapeSortName(s.getSortName()) + "12K\")}";
					sdf += "\n";
					sdf += "} .> {\n";
					for (Sort ss : userSorts) {
						if (!ss.isBaseSort() && (ss.equals(s) || sbs.contains(new Subsort(s, ss)))) {
							sdf += "        " + StringUtil.escapeSortName(ss.getSortName()) + " -> K";
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
			for (Sort s : userSorts) {
				if (!s.isBaseSort()) {
					sdf += "	K -> " + StringUtil.escapeSortName(s.getSortName());
					// sdf += " {cons(\"" + StringUtil.escapeSortName(s.getSortName()) + "12K\")}";
					sdf += "\n";
				}
			}
			sdf += "} .> {\n";
			for (Sort s : userSorts) {
				if (!s.isBaseSort()) {
					sdf += "	" + StringUtil.escapeSortName(s.getSortName()) + " -> K";
					// sdf += " {cons(\"K12" + StringUtil.escapeSortName(s.getSortName()) + "\")}";
					sdf += "\n";
				}
			}
			sdf += "}\n";
		}

		sdf += "context-free syntax\n";

		for (Production p : outsides) {
			if (p.isListDecl()) {
				UserList si = (UserList) p.getItems().get(0);
				sdf += "	" + StringUtil.escapeSortName(si.getSort().getSortName()) + " \"" + si.getTerminal() + "\" " + StringUtil.escapeSortName(p.getProdSort().getSortName()) + " -> " + StringUtil.escapeSortName(p.getProdSort().getSortName());
				sdf += " {cons(\"" + p.getAttributes().get("cons") + "\")}\n";
				sdf += "	\"." + p.getProdSort().getSortName() + "\" -> " + StringUtil.escapeSortName(p.getProdSort().getSortName());
				sdf += " {cons(\"" + StringUtil.escapeSortName(p.getProdSort().getSortName()) + "1Empty\")}\n";
			} else if (p.getAttributes().containsKey("bracket")) {
				// don't add bracket attributes added by the user
			} else {
				sdf += "	";
				List<Item> items = p.getItems();
				for (int i = 0; i < items.size(); i++) {
					Item itm = items.get(i);
					if (itm.getType() == ItemType.TERMINAL) {
						Terminal t = (Terminal) itm;
						if (t.getTerminal().equals(":"))
							sdf += "DouaPuncteDz ";
						else
							sdf += "\"" + t.getTerminal() + "\" ";
					} else if (itm.getType() == ItemType.SORT) {
						Sort srt = (Sort) itm;
						sdf += StringUtil.escapeSortName(srt.getSortName()) + " ";
					}
				}
				sdf += "-> " + StringUtil.escapeSortName(p.getProdSort().getSortName());
				sdf += getSDFAttributes(p.getAttributes()) + "\n";
			}
		}
		for (Sort ss : sorts)
			sdf += "	" + StringUtil.escapeSortName(ss.getSortName()) + " -> InsertDz" + StringUtil.escapeSortName(ss.getSortName()) + "\n";

		sdf += "\n\n";
		// print variables, HOLEs
		for (Sort s : userSorts) {
			if (!s.isBaseSort()) {
				sdf += "	VARID  \":\" \"" + s.getSortName() + "\"        -> VariableDz            {cons(\"" + StringUtil.escapeSortName(s.getSortName()) + "12Var\")}\n";
			}
		}
		sdf += "\n";
		for (Sort s : userSorts) {
			if (!s.isBaseSort()) {
				sdf += "	\"HOLE\" \":\" \"" + s.getSortName() + "\"      -> VariableDz            {cons(\"" + StringUtil.escapeSortName(s.getSortName()) + "12Hole\")}\n";
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
		for (Production p : constants) {
			sdf += "	\"" + p.getItems().get(0) + "\" -> Dz" + StringUtil.escapeSortName(p.getProdSort().getSortName()) + "\n";
		}

		sdf += "\n\n%% sort predicates\n";
		// print is<Sort> predicates (actually KLabel)
		for (Sort s : userSorts) {
			sdf += "	\"is" + s.getSortName() + "\"      -> DzKLabel\n";
		}

		sdf += "\n\n";

		sdf += "\n%% terminals reject\n";
		for (Terminal t : getTerminals(false)) {
			if (t.getTerminal().matches("$?[A-Z][^\\:\\;\\(\\)\\<\\>\\~\\n\\r\\t\\,\\ \\[\\]\\=\\+\\-\\*\\/\\|\\{\\}\\.]*")) {
				sdf += "	\"" + t.getTerminal() + "\" -> VARID {reject}\n";
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
}
