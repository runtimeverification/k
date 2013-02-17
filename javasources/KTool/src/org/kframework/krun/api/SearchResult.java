package org.kframework.krun.api;

import org.kframework.kil.Term;

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

	public Map<String, Term> getSubstitution() {
		return substitution;
	}

	public KRunState getState() {
		return state;
	}
}
