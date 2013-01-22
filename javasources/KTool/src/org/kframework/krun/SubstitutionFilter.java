package org.kframework.krun;

import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.*;

import java.util.Map;

public class SubstitutionFilter extends CopyOnWriteTransformer {

	private Map<String, Term> args;

	public SubstitutionFilter(Map<String, Term> args) {
		super("Plug terms into variables");
		this.args = args;
	}

	@Override
	public ASTNode transform(Variable var) {
		Term t = args.get(var.getName());
		if (t instanceof BackendTerm) {
			t.setSort(var.getSort());
		}
		return t;
	}
}
