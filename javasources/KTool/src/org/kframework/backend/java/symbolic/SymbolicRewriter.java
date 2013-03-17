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

	// public static void main(String[] args){
	// KList patternGuts = new KList();
	// KList termGuts = new KList();
	// KList subtermGuts = new KList();
	// KList rhsGuts = new KList();
	// patternGuts.add(new Variable("x", "KLabel"));
	// patternGuts.add(new Variable("y", "KLabel"));
	// patternGuts.add(new Variable("z", "K"));
	// patternGuts.add(new Variable("x", "KLabel"));
	// subtermGuts.add(Constant.KLABEL("d"));
	// subtermGuts.add(Constant.KLABEL("e"));
	// KApp subterm = new KApp(Constant.KLABEL("bar"), subtermGuts);
	// termGuts.add(Constant.KLABEL("a"));
	// termGuts.add(Constant.KLABEL("b"));
	// termGuts.add(subterm);
	// termGuts.add(Constant.KLABEL("a"));
	// rhsGuts.add(Constant.KLABEL("42"));
	// rhsGuts.add(new Variable("x", "KLabel"));
	// rhsGuts.add(new Variable("z", "K"));
	// KApp pattern = new KApp(Constant.KLABEL("foo"), patternGuts);
	// KApp term = new KApp(Constant.KLABEL("foo"), termGuts);
	// KApp rhs = new KApp(Constant.KLABEL("car"), rhsGuts);
	// System.out.println(pattern);
	// System.out.println(term);
	// Matcher m = new SimpleMatcher();
	// pattern.accept(m, term);
	// System.out.println(m.getSubstitution());
	// System.out.println("==================");
	// RewriteSet trs = new RewriteSet();
	// trs.add(new Rewrite(pattern, rhs));
	// System.out.println(trs);
	// System.out.println("==============>");
	// System.out.println(rewrite(trs, term));
	// System.out.println("==================");
	// //add another rewrite that matches the rhs of the previous rewrite
	// //and just rewrites to variable z
	// trs.add(new Rewrite(rhs, new Variable("z", "K")));
	// //add another rewrite that matches z from above (which is java variable subterm)
	// trs.add(new Rewrite(subterm, Constant.KLABEL("DONE")));
	// System.out.println(trs);
	// System.out.println("rewrite 1: " + rewriteN(trs,term,1)); //should print same as last time
	// System.out.println("rewrite 2: " + rewriteN(trs,term,2)); //should print bar(d ,, e)
	// System.out.println("rewrite 3: " + rewriteN(trs,term,3)); //should print DONE
	// System.out.println("rewrite normal form: " + rewriteToNormalForm(trs,term)); //should print DONE
	// System.out.println("=========map rewrite==========");
	// trs = new RewriteSet();
	// MapItem lm1 = new MapItem(Constant.KLABEL("bar"), Constant.KLABEL("foo"));
	// MapItem rm1 = new MapItem(Constant.KLABEL("ouch"), Constant.KLABEL("hcuo"));
	// Variable rem = new Variable("E", "Map");
	// java.util.List<Term> lmg = new ArrayList<Term>();
	// java.util.List<Term> rmg = new ArrayList<Term>();
	// lmg.add(lm1);
	// lmg.add(rem);
	// rmg.add(rm1);
	// rmg.add(rem);
	// MapLookupPattern l = new MapLookupPattern(new Map(lmg));
	// MapInsertPattern r = new MapInsertPattern(new Map(rmg));
	// System.out.println(l);
	// System.out.println(r);
	// trs.add(new Rewrite(l,r));
	// System.out.println(trs);
	// MapImpl mi = new MapImpl();
	// mi.put(Constant.KLABEL("bar"), Constant.KLABEL("foo"));
	// mi.put(Constant.KLABEL("car"), Constant.KLABEL("foo"));
	// mi.put(Constant.KLABEL("sar"), Constant.KLABEL("foo"));
	// System.out.println("initial: " + mi);
	// System.out.println("normal form: " + rewriteToNormalForm(trs, mi));
	// System.out.println("========more complicated map rewrite========");
	// patternGuts.add(l);
	// rhsGuts.add(r);
	// termGuts.add(mi);
	// mi.remove(Constant.KLABEL("ouch"));
	// mi.put(Constant.KLABEL("bar"), Constant.KLABEL("foo"));
	// trs = new RewriteSet();
	// pattern = new KApp(Constant.KLABEL("foo"), patternGuts);
	// term = new KApp(Constant.KLABEL("foo"), termGuts);
	// rhs = new KApp(Constant.KLABEL("car"), rhsGuts);
	// trs.add(new Rewrite(pattern, rhs));
	// System.out.println(trs);
	// System.out.println("initial: " + term);
	//
	// System.out.println("normal form: " + rewriteToNormalForm(trs, term));
	// }
}
