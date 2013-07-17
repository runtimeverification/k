package org.kframework.kcheck.utils;

import java.util.List;

import org.kframework.kil.Rewrite;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class ReachabilityRuleKILParser extends BasicVisitor {

	private final String ML_KLABEL = "'_/\\ML_";
	private Term pi;
	private Term phi;
	private Term pi_prime;
	private Term phi_prime;

	public ReachabilityRuleKILParser(Context context) {
		super(context);
	}

	public void visit(Rewrite node) {
		Term left = node.getLeft();
		Term right = node.getRight();

		if (left instanceof TermCons && right instanceof TermCons) {
			TermCons lcons = (TermCons) left;
			TermCons rcons = (TermCons) right;

			if (lcons.getProduction().getKLabel().equals(ML_KLABEL)
					&& rcons.getProduction().getKLabel().equals(ML_KLABEL)) {
				
				
				List<Term> leftTerms = lcons.getContents();
				pi = leftTerms.get(0);
				phi = leftTerms.get(1);
				
				List<Term> rightTerms = rcons.getContents();
				pi_prime = rightTerms.get(0);
				phi_prime = rightTerms.get(1);
			}
		}
	}

	public String getML_KLABEL() {
		return ML_KLABEL;
	}

	public Term getPi() {
		return pi;
	}

	public Term getPhi() {
		return phi;
	}

	public Term getPi_prime() {
		return pi_prime;
	}

	public Term getPhi_prime() {
		return phi_prime;
	}
}
