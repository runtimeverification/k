package org.kframework.compile.checks;

import java.util.HashMap;

import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sentence;
import org.kframework.kil.Sort;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
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

	public CheckSyntaxDecl(Context context) {
		super(context);
	}

	java.util.Map<Production, Production> prods = new HashMap<Production, Production>();

	@Override
	public void visit(Production node) {

		if (prods.containsKey(node)) {
			Production oldProd = prods.get(node);
			String msg = "Production has already been defined at " + oldProd.getLocation() + " in file " + oldProd.getFilename();
			GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
		} else
			prods.put(node, node);

		int sorts = 0;
		int neTerminals = 0;
		int eTerminals = 0;

		if (node.isSubsort()) {
			String sort = ((Sort) node.getItems().get(0)).getName();
			if (Sort.isBasesort(sort) && !context.isSubsorted(node.getSort(), sort)) {
				String msg = "Extending  built-in sorts is forbidden: K, KResult, KList, Map,\n\t MapItem, List, ListItem, Set, SetItem, Bag, BagItem, KLabel, CellLabel";
				GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
			}
		}

		for (ProductionItem pi : node.getItems()) {
			if (pi instanceof Sort) {
				sorts++;
				Sort s = (Sort) pi;
				if (!(s.getName().endsWith("CellSort") || s.getName().endsWith("CellFragment")))
					if (!s.getName().startsWith("#") && !context.definedSorts.contains(s.getName())) {
						String msg = "Undefined sort " + s.getName();
						GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), s.getFilename(), s.getLocation()));
					}
				if (s.getName().equals("KResult") && !(node.isSubsort() && node.getSort().equals("K"))) {
					String msg = "KResult is only allowed in the left hand side of syntax.";
					GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), s.getFilename(), s.getLocation()));
				}
			}
			if (pi instanceof UserList) {
				sorts++;
				UserList s = (UserList) pi;
				if (!s.getSort().startsWith("#") && !context.definedSorts.contains(s.getSort())) {
					String msg = "Undefined sort " + s.getSort();
					GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), s.getFilename(), s.getLocation()));
				}
				if (s.getSort().equals("KResult")) {
					String msg = "KResult is only allowed in the left hand side of syntax declarations.";
					GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), s.getFilename(), s.getLocation()));
				}
			}
			if (pi instanceof Terminal) {
				Terminal t = (Terminal) pi;
				if (t.getTerminal().equals(""))
					eTerminals++;
				else
					neTerminals++;
			}
		}

		if (eTerminals > 0 && (neTerminals == 0 || sorts < 2))
			if (!node.containsAttribute("onlyLabel") || !node.containsAttribute("klabel")) {
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
