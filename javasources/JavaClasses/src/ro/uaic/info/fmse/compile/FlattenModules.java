package ro.uaic.info.fmse.compile;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

import ro.uaic.info.fmse.k.Configuration;
import ro.uaic.info.fmse.k.Definition;
import ro.uaic.info.fmse.k.DefinitionItem;
import ro.uaic.info.fmse.k.Module;
import ro.uaic.info.fmse.k.Import;
import ro.uaic.info.fmse.k.ModuleItem;
import ro.uaic.info.fmse.visitors.BasicVisitor;

public class FlattenModules extends BasicVisitor {
	HashMap<String,Module> modules = new HashMap<String,Module>();
	Definition result = new Definition();
	
	@Override
	public void visit(Definition d) {
		Set<String> included = new HashSet<String>();
		Configuration cfg = null;
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
					String imp = ((Import)i).getName();
					if (included.contains(imp)) continue;
					if (!MetaK.isKModule(imp) && !MetaK.isBuiltinModule(imp)) {
						if (modules.containsKey(imp)) {
							mods.add(modules.remove(imp));
							included.add(imp);
//							System.out.println("push " + imp);
							continue;
						}					
					} else included.add(imp);
				}
				if (i instanceof Configuration) {
					if (null == cfg) 
						cfg = (Configuration)i;
					continue;
				}
//				System.out.println(i.toString());
				rmod.getItems().add(i);
			}
		}		
	}

	
	@Override
	public void visit(Module m) {
		modules.put(m.getName(), m);
	}
	
	public Definition getResult() {
		return result;
	}
}
