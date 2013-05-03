package org.kframework.krun.api;

import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.SubstitutionFilter;
import org.kframework.utils.general.GlobalSettings;

import java.util.HashMap;
import java.util.Map;

public class SearchResult {
	private KRunState state;
	private Map<String, Term> substitution;
	private Map<String, Term> rawSubstitution;

	public SearchResult(KRunState state, Map<String, Term> rawSubstitution, RuleCompilerSteps compilationInfo) throws TransformerException {
		this.state = state;
		this.rawSubstitution = rawSubstitution;
		substitution = new HashMap<String, Term>();
		for (Variable var : compilationInfo.getVars()) {
			Term rawValue;
			if (GlobalSettings.sortedCells) {
				Term cellFragment = compilationInfo.getCellFragment(var);
				rawValue = (Term)cellFragment.accept(new SubstitutionFilter(rawSubstitution));
			} else {
				rawValue = rawSubstitution.get(var.getName() + ":" + var.getSort());
			}
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
