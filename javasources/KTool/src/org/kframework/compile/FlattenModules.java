package org.kframework.compile;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

import org.kframework.compile.utils.CompilerStep;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;


public class FlattenModules  implements CompilerStep {
	@Override
	public Definition compile(Definition def) {
		FlattenModulesVisitor fm = new FlattenModulesVisitor();
		def.accept(fm);
		return fm.getResult();
	}

	private class FlattenModulesVisitor extends BasicVisitor  {
		HashMap<String,Module> modules = new HashMap<String,Module>();
		Definition result = new Definition();

		@Override
		public void visit(Definition d) {
			Set<String> included = new HashSet<String>();
			Configuration cfg = null;
//			boolean nextId = false;
			super.visit(d);
			result.setFilename(d.getFilename());
			result.setLocation(d.getLocation());
			result.setMainFile(d.getMainFile());
			result.setMainModule(d.getMainModule());
			result.setMainSyntaxModule(d.getMainModule());
			result.setItems(new ArrayList<DefinitionItem>());
			Queue<Module> mods = new LinkedList<Module>();
			Module rmod = new Module();
			rmod.setName(d.getMainModule());
			rmod.setType("module");
			rmod.setItems(new ArrayList<ModuleItem>());
			result.getItems().add(rmod);
			mods.add(modules.remove(d.getMainModule()));
			//		System.out.println("push " + d.getMainModule());
			while (!mods.isEmpty()) {
				Module mod = mods.remove();
				//			System.out.println("pop " + mod.getName());
				if (null == mod.getItems()) continue;
				for(ModuleItem i : mod.getItems()) {
					if (i instanceof Import) {
						String name = ((Import)i).getName();
//						if (MetaK.isNextIdModule(name)) 
//							nextId = true;
						if (included.contains(name)) continue;
						if (!MetaK.isKModule(name) && !MetaK.isBuiltinModule(name)) {
							if (modules.containsKey(name)) {
								mods.add(modules.get(name));
								included.add(name);
								//							System.out.println("push " + imp);
							} else {
								GlobalSettings.kem.register(new KException(ExceptionType.WARNING, 
										KExceptionGroup.COMPILER, 
										"Module " + name + " undefined.", 
										i.getFilename(), i.getLocation(), 0));
							}
							continue;
						} else included.add(name);
					}
					if (i instanceof Configuration) {
						if (null == cfg) 
							cfg = (Configuration)i;
						//					System.out.println(i.toMaude());
						continue;
					}
					//				System.out.println(i.toString());
					rmod.getItems().add(i);
				}
			}
			if (null == cfg) {
				cfg = new Configuration();
				Cell k = new Cell();
				k.setLabel("k");
				k.setElipses("none");
				k.setSort("K");
				k.setContents(new Variable("$PGM","K"));
				cfg.setBody(k);
			}
//			if (nextId) {
//				Bag bag;
//				if (cfg.getBody() instanceof Bag) {
//					bag = (Bag) cfg.getBody();
//				} else {
//					bag = new Bag();
//					bag.getContents().add(cfg.getBody());
//					cfg.setBody(bag);
//				}
//				Cell nId = new Cell();
//				nId.setLabel("nextId");
//				nId.setElipses("none");
//				Constant zero = new Constant("Int", "0");
//				nId.setContents(zero);
//				bag.getContents().add(nId);
//			}
			if (null != cfg)
				rmod.getItems().add(cfg);
		}

		@Override
		public void visit(Module m) {
			modules.put(m.getName(), m);
		}

		public Definition getResult() {
			return result;
		}
	}

	@Override
	public String getName() {
		return "Flatten Modules";
	}
}
