package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.List;

import org.kframework.backend.symbolic.SymbolicBackend;
import org.kframework.kil.Attribute;
import org.kframework.kil.Definition;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Term;

/**
 * Created with IntelliJ IDEA. User: andrei Date: 3/12/13 Time: 4:03 PM To change this template use File | Settings | File Templates.
 */
public class SymbolicRewriter {

	public class Rule {
		private final Term leftHandSide;
		private final Term rightHandSide;
		private final Term condition;

		public Rule(Term leftHandSide, Term rightHandSide, Term condition) {
			this.leftHandSide = leftHandSide;
			this.rightHandSide = rightHandSide;
			this.condition = condition;
		}

		public Rule(Term leftHandSide, Term rightHandSide) {
			this(leftHandSide, rightHandSide, null);
		}

		public Term getLeftHandSide() {
			return leftHandSide;
		}

		public Term getRightHandSide() {
			return rightHandSide;
		}

		public boolean hasCondition() {
			return condition != null;
		}

		public Term getCondition() {
			assert hasCondition();

			return condition;
		}
	}

	private final SymbolicMatcher matcher;
	private final List<Rule> rules;

	public SymbolicRewriter(Definition definition) {
		matcher = new SymbolicMatcher();

		rules = new ArrayList<Rule>(definition.getSingletonModule().getRules().size());
		for (org.kframework.kil.Rule kilRule : definition.getSingletonModule().getRules()) {
			if (!kilRule.containsAttribute(SymbolicBackend.SYMBOLIC) || kilRule.containsAttribute(Attribute.FUNCTION.getKey()) || kilRule.containsAttribute(Attribute.PREDICATE.getKey())
					|| kilRule.containsAttribute(Attribute.ANYWHERE.getKey())) {
				continue;
			}

			assert kilRule.getBody() instanceof Rewrite;

			Rewrite rewrite = (Rewrite) kilRule.getBody();
			rules.add(new Rule(rewrite.getLeft(), rewrite.getRight(), kilRule.getCondition()));

			// System.err.println(kilRule);
			// System.err.println("===");
		}
	}

	public Rule getRule(org.kframework.kil.Rule kilRule) {
		if (kilRule.getBody() instanceof Rewrite) {

		}

		return null;
	}

	public Term rewrite(Term term) {
		for (Rule rule : rules) {
			if (matcher.isMatching(term, rule.leftHandSide)) {
				System.err.println(rule.leftHandSide);
			}
		}

		return term;
	}
}
