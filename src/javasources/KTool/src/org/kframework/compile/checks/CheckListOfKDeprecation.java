package org.kframework.compile.checks;

import org.kframework.kil.KSorts;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
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
public class CheckListOfKDeprecation extends BasicVisitor {

	public CheckListOfKDeprecation(Context context) {
		super(context);
	}

	@Override
	public void visit(Sort node) {
		if (node.getName().equals("List{K}")) {
			String msg = "Deprecated: List{K} has been renamed into KList to be less confuzing.";
			GlobalSettings.kem.register(new KException(KException.ExceptionType.WARNING, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
			node.setName(KSorts.KLIST);
		}
	}

	@Override
	public void visit(Term node) {
		if (node.getSort().equals("List{K}")) {
			String msg = "Deprecated: List{K} has been renamed into KList to be less confuzing.";
			GlobalSettings.kem.register(new KException(KException.ExceptionType.WARNING, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
			node.setSort(KSorts.KLIST);
		}
	}
}
