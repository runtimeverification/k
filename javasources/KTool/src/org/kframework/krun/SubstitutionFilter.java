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
		return args.get(var.getName());
	}
}
