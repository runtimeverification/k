package org.kframework.compile.checks;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.HashMap;
import java.util.Map;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 11/21/12
 * Time: 3:13 PM
 */
public class CheckVariables extends BasicVisitor {

	HashMap<Variable, Integer> left = new HashMap<Variable, Integer>();
	HashMap<Variable, Integer> right = new HashMap<Variable, Integer>();
	HashMap<Variable, Integer> current = left;
	boolean inCondition = false;

	@Override
	public void visit(Rewrite node) {
		node.getLeft().accept(this);
		current = right;
		node.getRight().accept(this);
		current = left;
	}

	@Override
	public void visit(Variable node) {
		Integer i = current.remove(node);
		if (i == null) {
			i = new Integer(1);
		} else {
			i = new Integer(i.intValue() + 1);
		}
		current.put(node, i);
	}

	@Override
	public void visit(Configuration node) {
		return;
	}

	@Override
	public void visit(Syntax node) {
		return;
	}

	@Override
	public void visit(TermCons node) {
		if (!node.getCons().equals(MetaK.Constants.freshCons)) {
			super.visit(node);
			return;
		}
		if (!inCondition) {
			GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR,
					KException.KExceptionGroup.COMPILER,
					"Fresh can only be used in conditions.",
					getName(), node.getFilename(), node.getLocation()));
		}
		final Term term = node.getContents().get(0);
		if (!(term instanceof  Variable)) {
			GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR,
					KException.KExceptionGroup.COMPILER,
					"Fresh can only be applied to variables, but was applied to\n\t\t" + term,
					getName(), term.getFilename(), term.getLocation()));
		}
		Variable v = (Variable) term;
		if (left.containsKey(v)) {
			for (Variable v1 : left.keySet()) {
				if (v1.equals(v)) {
					GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR,
							KException.KExceptionGroup.COMPILER,
							"Fresh variable \"" + v1 + "\" is bound in the rule pattern.",
							getName(), v1.getFilename(), v1.getLocation()));
				}
			}
		}
		left.put(v, new Integer(1));
	}

	@Override
	public void visit(Sentence node) {
		inCondition = false;
		left.clear();
		right.clear();
		current = left;
		node.getBody().accept(this);
		if (node.getCondition() != null) {
			current = right;
			inCondition = true;
			node.getCondition().accept(this);
		}
		for (Variable v : right.keySet()) {
			if (!left.containsKey(v)) {
				GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR,
						KException.KExceptionGroup.COMPILER,
						"Unbounded Variable " + v.toString() + ".",
						getName(), v.getFilename(), v.getLocation()));
			}
		}
		for (Map.Entry<Variable,Integer> e : left.entrySet()) {
			final Variable key = e.getKey();
			if (MetaK.isAnonVar(key)) continue;
			if (e.getValue().intValue()>1) continue;
			if (!right.containsKey(key)) {
				GlobalSettings.kem.register(new KException(KException.ExceptionType.HIDDENWARNING,
						KException.KExceptionGroup.COMPILER,
						"Unused named variable " + key.toString() + ".",
						getName(), key.getFilename(), key.getLocation()));
			}
		}
	}
}
