package org.kframework.compile.checks;

import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.Sentence;
import org.kframework.kil.Sort;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

/**
 * Check for various errors in syntax declarations. 1. You are not allowed to use empty terminals ("") in definitions. You need to have at least two sorts, or a non empty terminal.
 * 
 * @author Radu
 * 
 */
public class CheckSyntaxDecl extends BasicVisitor {

	@Override
	public void visit(Production node) {
		int sorts = 0;
		int neTerminals = 0;
		int eTerminals = 0;
		for (ProductionItem pi : node.getItems()) {
			if (pi.getType() == ProductionType.SORT) {
				sorts++;
				Sort s = (Sort) pi;
				if (!s.getName().startsWith("#") && !DefinitionHelper.definedSorts.contains(s.getName())) {
					String msg = "Undefined sort " + s.getName();
					GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), s.getFilename(), s.getLocation()));
				}
			}
			if (pi.getType() == ProductionType.USERLIST) {
				sorts++;
				UserList s = (UserList) pi;
				if (!s.getSort().startsWith("#") && !DefinitionHelper.definedSorts.contains(s.getSort())) {
					String msg = "Undefined sort " + s.getSort();
					GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), s.getFilename(), s.getLocation()));
				}
			}
			if (pi.getType() == ProductionType.TERMINAL) {
				Terminal t = (Terminal) pi;
				if (t.getTerminal().equals(""))
					eTerminals++;
				else
					neTerminals++;
			}
		}

		if (eTerminals > 0 && (neTerminals == 0 || sorts < 2))
			if (!node.getAttributes().containsKey("onlyLabel") || !node.getAttributes().containsKey("klabel")) {
				String msg = "Cannot declare empty terminals in the definition.\n";
				msg += "            Use attribute 'onlyLabel' paired with 'klabel(...)' to limit the use to programs.";
				GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
			}
	}

	@Override
	public void visit(Sentence node) {
		// optimization to not visit the entire tree
	}
}
