package org.kframework.parser.generator;

import java.util.HashSet;
import java.util.List;

import org.kframework.compile.transformers.AddPredicates;
import org.kframework.compile.transformers.AddSymbolicK;
import org.kframework.kil.Definition;
import org.kframework.kil.Lexical;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Restrictions;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.Sort;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Subsort;
import org.kframework.utils.StringUtil;

public class Definition2SDF {

	public static String getSdfForDefinition(Definition def) {

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
				// sdf.append(" {cons(\"K12" + StringUtil.escapeSortName(s.getName()) + "\")}");
				sdf.append("\n");
			}
		}
		sdf.append("} > {\n");
		for (Subsort subs : psdfv.subsorts) {
			String s1 = subs.getSmallSort();
			String s2 = subs.getBigSort();
			if (!Sort.isBasesort(s1) && !Sort.isBasesort(s2)) {
				sdf.append("	" + StringUtil.escapeSortName(s1) + " -> " + StringUtil.escapeSortName(s2));
				// sdf.append(" {cons(\"" + StringUtil.escapeSortName(s2) + "12" + StringUtil.escapeSortName(s1) + "\")}");
				sdf.append("\n");
			}
		}
		sdf.append("} > {\n");
		for (Sort s : psdfv.userSorts) {
			if (!s.isBaseSort()) {
				sdf.append("	K -> " + StringUtil.escapeSortName(s.getName()));
				// sdf.append(" {cons(\"" + StringUtil.escapeSortName(s.getName()) + "12K\")}");
				sdf.append("\n");
			}
		}
		sdf.append("}\n\n");

		sdf.append("%% subsorts 2\n");
		// print K -> Sort > Sort -> K
		sdf.append("context-free priorities\n{\n");
		for (Sort s : psdfv.userSorts) {
			if (!s.isBaseSort()) {
				sdf.append("	K -> " + StringUtil.escapeSortName(s.getName()));
				// sdf.append(" {cons(\"" + StringUtil.escapeSortName(s.getName()) + "12K\")}");
				sdf.append("\n");
			}
		}
		sdf.append("} .> {\n");
		for (Sort s : psdfv.userSorts) {
			if (!s.isBaseSort()) {
				sdf.append("	" + StringUtil.escapeSortName(s.getName()) + " -> K");
				// sdf.append(" {cons(\"K12" + StringUtil.escapeSortName(s.getName()) + "\")}");
				sdf.append("\n");
			}
		}
		sdf.append("}\n");

		sdf.append("context-free syntax\n");

		for (Production p : psdfv.outsides) {
			if (p.isListDecl()) {
				UserList si = (UserList) p.getItems().get(0);
				sdf.append("	" + StringUtil.escapeSortName(si.getSort()) + " \"" + si.getSeparator() + "\" " + StringUtil.escapeSortName(p.getSort()) + " -> " + StringUtil.escapeSortName(p.getSort()));
				sdf.append(" {cons(\"" + p.getAttribute("cons") + "\")}\n");
				sdf.append("	\"." + p.getSort() + "\" -> " + StringUtil.escapeSortName(p.getSort()));
				sdf.append(" {cons(\"" + StringUtil.escapeSortName(p.getSort()) + "1Empty\")}\n");
			} else if (p.containsAttribute("bracket")) {
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
							sdf.append("\"" + StringUtil.escape(t.getTerminal()) + "\" ");
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
		for (String sort : psdfv.constantSorts) {
			String s = StringUtil.escapeSortName(sort);
			sdf.append("	Dz" + s + "		-> " + s + "	{cons(\"" + s + "1Const\")}\n");
		}

		sdf.append("\n");
		sdf.append("	DzDzINT		-> DzDzInt\n");
		sdf.append("	DzDzID		-> DzDzId\n");
		sdf.append("	DzDzSTRING	-> DzDzString\n");
		sdf.append("	DzDzFLOAT	-> DzDzFloat\n");
		sdf.append("	\":\" -> DouaPuncteDz {cons(\"DouaPuncte\")}\n");

		sdf.append("\n");

		sdf.append("context-free restrictions\n");
		sdf.append("	DouaPuncteDz -/- [A-Z]\n\n");

		sdf.append("lexical syntax\n");
		for (Production p : psdfv.constants) {
			sdf.append("	" + p.getItems().get(0) + " -> Dz" + StringUtil.escapeSortName(p.getSort()) + "\n");
		}

		sdf.append("\n\n%% sort predicates\n");
		// print is<Sort> predicates (actually KLabel)
		for (Sort s : psdfv.userSorts) {
			sdf.append("	\"" + AddPredicates.syntaxPredicate(s.getName()) + "\"      -> DzKLabel\n");
			sdf.append("	\"" + AddPredicates.symbolicPredicate(s.getName()) + "\"      -> DzKLabel\n");
			sdf.append("	\"" + AddSymbolicK.symbolicConstructor(s.getName()) + "\"      -> DzKLabel\n");
		}

		sdf.append("\n\n");

		sdf.append("\n%% terminals reject\n");
		for (String t : terminals.terminals) {
			if (t.matches("$?[A-Z][^\\:\\;\\(\\)\\<\\>\\~\\n\\r\\t\\,\\ \\[\\]\\=\\+\\-\\*\\/\\|\\{\\}\\.]*")) {
				sdf.append("	\"" + t + "\" -> VARID {reject}\n");
			}
		}

		sdf.append("\n\n");
		for (String t : terminals.terminals) {
			if (t.matches("[a-zA-Z][a-zA-Z0-9]*")) {
				sdf.append("	\"" + t + "\" -> DzDzID {reject}\n");
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

		// lexical rules
		sdf.append("lexical syntax\n");
		java.util.Set<String> lexerSorts = new HashSet<String>();
		for (Production p : psdfv.lexical) {
			Lexical l = (Lexical) p.getItems().get(0);
			lexerSorts.add(p.getSort());
			sdf.append("	" + l.getLexicalRule() + " -> " + StringUtil.escapeSortName(p.getSort()) + "Dz\n");
			if (l.getFollow() != null && !l.getFollow().equals("")) {
				psdfv.restrictions.add(new Restrictions(p.getSort(), null, l.getFollow()));
			}
		}

		// adding cons over lexical rules
		sdf.append("context-free syntax\n");
		for (String s : lexerSorts) {
			sdf.append("	" + StringUtil.escapeSortName(s) + "Dz -> " + StringUtil.escapeSortName(s) + " {cons(\"" + StringUtil.escapeSortName(s) + "1Const\")}\n");
		}
		sdf.append("\n\n");

		// follow restrictions
		sdf.append("lexical restrictions\n");
		for (Restrictions r : psdfv.restrictions) {
			if (r.getTerminal() != null && !r.getTerminal().getTerminal().equals(""))
				sdf.append("	" + r.getTerminal() + " -/- " + r.getPattern() + "\n");
			else
				sdf.append("	" + StringUtil.escapeSortName(r.getSort().getName()) + " -/- " + r.getPattern() + "\n");
		}

		return sdf.toString();
	}
}
