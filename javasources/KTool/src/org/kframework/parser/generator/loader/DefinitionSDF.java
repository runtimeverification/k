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
import org.kframework.utils.Error;
import org.kframework.utils.StringUtil;


public class DefinitionSDF {

	public static String getSdfForPrograms(Definition def) {

		Set<Module> synMods = new HashSet<Module>();
		List<Module> synQue = new LinkedList<Module>();
		synQue.add(def.getModulesMap().get(def.getMainSyntaxModule()));

		Module bshm = def.getModulesMap().get("BUILTIN-SYNTAX-HOOKS");
		if (bshm != null)
			synQue.add(bshm);
		else
			Error.silentReport("Could not find module BUILTIN-SYNTAX-HOOKS (automatically included in the main syntax module)!");

		while (!synQue.isEmpty()) {
			Module m = synQue.remove(0);
			if (!synMods.contains(m)) {
				synMods.add(m);
				CollectIncludesVisitor civ = new CollectIncludesVisitor();
				m.accept(civ);
				List<Import> ss = civ.getImportList();
				for (Import s : ss) {
					String mname = s.getName();
					Module mm = def.getModulesMap().get(mname);
					// if the module starts with # it means it is predefined in maude
					if (!mname.startsWith("#"))
						if (mm != null)
							synQue.add(mm);
						else if (!MetaK.isKModule(mname))
							Error.silentReport("Could not find module: " + mname + " imported from: " + m.getName());
				}
			}
		}

		Definition def2 = new Definition(def);
		def2.setItems(new ArrayList<DefinitionItem>());
		def2.getItems().addAll(synMods);

		String sdf = "module Program\n\n";
		sdf += "imports Common\n";
		sdf += "imports KBuiltinsBasic\n";
		sdf += "exports\n\n";
		sdf += "context-free syntax\n";

		// TODO: visit here
		ProgramSDFVisitor psdfv = new ProgramSDFVisitor();
		def2.accept(psdfv);

		sdf += "context-free start-symbols\n";
		sdf += "	Start\n";
		sdf += "context-free syntax\n";

		for (Production p : psdfv.outsides) {
			if (p.isListDecl()) {
				UserList si = (UserList) p.getItems().get(0);
				sdf += "	{" + StringUtil.escapeSortName(si.getSort()) + " \"" + si.getSeparator() + "\"}* -> " + StringUtil.escapeSortName(p.getSort()) + " {cons(" + p.getAttributes().get("cons") + ")}\n";
			} else {
				sdf += "	";
				List<ProductionItem> items = p.getItems();
				for (int i = 0; i < items.size(); i++) {
					ProductionItem itm = items.get(i);
					if (itm.getType() == ProductionType.TERMINAL) {
						Terminal t = (Terminal) itm;
						sdf += "\"" + t.getTerminal() + "\" ";
					} else if (itm.getType() == ProductionType.SORT) {
						Sort srt = (Sort) itm;
						sdf += StringUtil.escapeSortName(srt.getName()) + " ";
					}
				}
				sdf += "-> " + StringUtil.escapeSortName(p.getSort());
				sdf += SDFHelper.getSDFAttributes(p.getAttributes()) + "\n";
			}
		}

		for (String ss : psdfv.sorts)
			sdf += "	" + StringUtil.escapeSortName(ss) + " -> InsertDz" + StringUtil.escapeSortName(ss) + "\n";

		sdf += "\n%% start symbols\n";
		if (psdfv.startSorts.size() == 0) {
			for (String s : psdfv.userSort) {
				if (!s.equals("Start"))
					sdf += "	" + StringUtil.escapeSortName(s) + "		-> Start\n";
			}
		}

		sdf += "\n\n";
		sdf += "	DzDzInt		-> DzInt	{cons(\"DzInt1Const\")}\n";
		sdf += "	DzDzBool	-> DzBool	{cons(\"DzBool1Const\")}\n";
		sdf += "	DzDzId		-> DzId		{cons(\"DzId1Const\")}\n";
		sdf += "	DzDzString	-> DzString	{cons(\"DzString1Const\")}\n";

		sdf += "\n";
		sdf += "	DzDzINT		-> DzDzInt\n";
		sdf += "	DzDzID		-> DzDzId\n";
		sdf += "	DzDzBOOL	-> DzDzBool\n";
		sdf += "	DzDzSTRING	-> DzDzString\n";

		sdf += "\n";

		sdf += "lexical syntax\n";
		for (Production prd : psdfv.constants) {
			sdf += "	\"" + prd.getItems().get(0) + "\" -> Dz" + StringUtil.escapeSortName(prd.getSort()) + "\n";
		}

		sdf += "\n\n";

		// TODO: uncomment and fix
		// for (Terminal t : getTerminals(true)) {
		// if (t.getTerminal().matches("[a-zA-Z][a-zA-Z0-9]*")) {
		// sdf += "	\"" + t.getTerminal() + "\" -> DzDzID {reject}\n";
		// }
		// }
		//
		// sdf += "\n";
		// sdf += getFollowRestrictionsForTerminals(true);

		sdf += "\n";

		return sdf;
	}
}
