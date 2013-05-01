package org.kframework.krun.api;

import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.SubstitutionFilter;

import java.util.HashMap;
import java.util.Map;

public class SearchResult {
	private KRunState state;
	private Map<String, Term> substitution;
	private Map<String, Term> rawSubstitution;

	public SearchResult(KRunState state, Map<String, Term> rawSubstitution) {
		this.state = state;
		this.rawSubstitution = rawSubstitution;
		substitution = new HashMap<String, Term>();
		for (String name : rawSubstitution.keySet()) {
			substitution.put(name, KRunState.concretize(rawSubstitution.get(name)));
		}
	}

	public SearchResult(KRunState state, Map<String, Term> rawSubstitution, RuleCompilerSteps compilationInfo) throws TransformerException {
		this.state = state;
		this.rawSubstitution = rawSubstitution;
		substitution = new HashMap<String, Term>();
		for (Variable var : compilationInfo.getVars()) {
			Term cellFragment = compilationInfo.getCellFragment(var);
			Term rawValue = (Term)cellFragment.accept(new SubstitutionFilter(rawSubstitution));
			substitution.put(var.getName() + ":" + var.getSort(), KRunState.concretize(rawValue));
		}
	}

	public Map<String, Term> getSubstitution() {
		return substitution;
	}

	public KRunState getState() {
		return state;
	}
}
