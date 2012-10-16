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
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.Sort;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

/**
 * Collect the syntax module, call the syntax collector and print SDF for programs.
 * 
 * @author RaduFmse
 * 
 */
public class ProgramSDF {

	public static String getSdfForPrograms(Definition def) {

		Set<Module> synMods = new HashSet<Module>();
		List<Module> synQue = new LinkedList<Module>();
		synQue.add(def.getModulesMap().get(def.getMainSyntaxModule()));

		Module bshm = def.getModulesMap().get("BUILTIN-SYNTAX-HOOKS");
		if (bshm != null)
			synQue.add(bshm);
		else {
			String msg = "Could not find module BUILTIN-SYNTAX-HOOKS (automatically included in the main syntax module)!";
			GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.PARSER, msg, def.getMainFile(), "File system."));
		}

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
						else if (!MetaK.isKModule(mname)) {
							String msg = "Could not find module: " + mname + " imported from: " + m.getName();
							GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.PARSER, msg, def.getMainFile(), "File system."));
						}
				}
			}
		}

		Definition def2 = new Definition(def);
		def2.setItems(new ArrayList<DefinitionItem>());
		def2.getItems().addAll(synMods);

		StringBuilder sdf = new StringBuilder();
		sdf.append("module Program\n\n");
		sdf.append("imports Common\n");
		sdf.append("imports KBuiltinsBasic\n");
		sdf.append("exports\n\n");
		sdf.append("context-free syntax\n");

		// TODO: visit here
		ProgramSDFVisitor psdfv = new ProgramSDFVisitor();
		def2.accept(psdfv);

		sdf.append("context-free start-symbols\n");
		sdf.append("	Start\n");
		sdf.append("context-free syntax\n");

		for (Production p : psdfv.outsides) {
			if (p.isListDecl()) {
				UserList si = (UserList) p.getItems().get(0);
				sdf.append("	{" + StringUtil.escapeSortName(si.getSort()) + " \"" + si.getSeparator() + "\"}* -> " + StringUtil.escapeSortName(p.getSort()) + " {cons(" + p.getAttributes().get("cons") + ")}\n");
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

		sdf.append("\n%% start symbols\n");
		if (psdfv.startSorts.size() == 0) {
			for (String s : psdfv.userSort) {
				if (!s.equals("Start"))
					sdf.append("	" + StringUtil.escapeSortName(s) + "		-> Start\n");
			}
		}

		sdf.append("\n\n");
		sdf.append("	DzDzInt		-> DzInt	{cons(\"DzInt1Const\")}\n");
		sdf.append("	DzDzBool	-> DzBool	{cons(\"DzBool1Const\")}\n");
		sdf.append("	DzDzId		-> DzId		{cons(\"DzId1Const\")}\n");
		sdf.append("	DzDzString	-> DzString	{cons(\"DzString1Const\")}\n");

		sdf.append("\n");
		sdf.append("	DzDzINT		-> DzDzInt\n");
		sdf.append("	DzDzID		-> DzDzId\n");
		sdf.append("	DzDzBOOL	-> DzDzBool\n");
		sdf.append("	DzDzSTRING	-> DzDzString\n");

		sdf.append("\n");

		sdf.append("lexical syntax\n");
		for (Production prd : psdfv.constants) {
			sdf.append("	\"" + prd.getItems().get(0) + "\" -> Dz" + StringUtil.escapeSortName(prd.getSort()) + "\n");
		}

		sdf.append("\n\n");

		// TODO: uncomment and fix
		// for (Terminal t : getTerminals(true)) {
		// if (t.getTerminal().matches("[a-zA-Z][a-zA-Z0-9]*")) {
		// sdf.append("	\"" + t.getTerminal() + "\" -> DzDzID {reject}\n";
		// }
		// }
		//
		// sdf.append("\n");
		// sdf.append(getFollowRestrictionsForTerminals(true));

		sdf.append("\n");

		return sdf.toString();
	}
}
