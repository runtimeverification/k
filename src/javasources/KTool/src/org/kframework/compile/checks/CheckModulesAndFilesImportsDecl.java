package org.kframework.compile.checks;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.parser.generator.CollectIncludesVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

public class CheckModulesAndFilesImportsDecl extends BasicVisitor {

	public CheckModulesAndFilesImportsDecl(Context context) {
		super(context);
	}

	@Override
	public void visit(Definition def) {

		for (DefinitionItem di : def.getItems()) {
			if (di instanceof Module && !di.isPredefined()) {
				Module m = (Module) di;
				CollectIncludesVisitor civ = new CollectIncludesVisitor(context);
				m.accept(civ);

				for (Import i : civ.getImportList()) {
					if (!i.getName().startsWith("#") && !MetaK.isBuiltinModule(i.getName())) {
						Module imported = def.getModulesMap().get(i.getName());
						if (imported == null || !context.isRequiredEq(imported.getFilename(), m.getFilename())) {
							String msg = "Could not find module: " + i.getName() + " imported from: " + m.getName();
							GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), m.getFilename(), i.getLocation()));
						}
					}
				}
			}
		}
	}
}
