package org.kframework.krun;

import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.ASTNode;

public class RuleInvocation {

	private ASTNode rule;

	public RuleInvocation(ASTNode rule) {
		this.rule = rule;
	}

	public ASTNode getRule() {
		return rule;
	}

	public void setRule(ASTNode rule) {
		this.rule = rule;
	}

	@Override
	public String toString() {
		UnparserFilter unparser = new UnparserFilter(true, K.color);
		rule.accept(unparser);
		return "\n" + unparser.getResult();
	}
}
