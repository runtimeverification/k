package org.kframework.compile.checks;

import java.util.HashMap;

import org.kframework.kil.KSorts;
import org.kframework.kil.Production;
import org.kframework.kil.Sentence;
import org.kframework.kil.Syntax;
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
public class CheckSortTopUniqueness extends BasicVisitor {
	public CheckSortTopUniqueness(Context context) {
		super(context);
	}

	java.util.Map<Production, Production> prods = new HashMap<Production, Production>();

	@Override
	public void visit(Syntax node) {
		String msg = "Multiple top sorts found for " + node.getSort() + ": ";
		int count = 0;
		if (context.isSubsorted(KSorts.KLIST, node.getSort().getName())) {
			msg += KSorts.KLIST + ", ";
			count++;
		}
		if (context.isSubsorted("List", node.getSort().getName())) {
			msg += "List, ";
			count++;
		}
		if (context.isSubsorted("Bag", node.getSort().getName())) {
			msg += "Bag, ";
			count++;
		}
		if (context.isSubsorted("Map", node.getSort().getName())) {
			msg += "Map, ";
			count++;
		}
		if (context.isSubsorted("Set", node.getSort().getName())) {
			msg += "Set, ";
			count++;
		}
		if (count > 1) {
			msg = msg.substring(0, msg.length() - 2);
			GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
		}
	}

	@Override
	public void visit(Sentence node) {
		// optimization to not visit the entire tree
	}
}
