package org.kframework.krun;

import org.kframework.kil.Term;

public class Transition {

	private Term term;
	private String label;

	public Transition(Term term, String label) {
		this.term = term;
		this.label = label;
	}

	public Term getTerm() {
		return term;
	}

	public String getLabel() {
		return label;
	}

	public void setTerm(Term term) {
		this.term = term;
	}

	public void setLabel(String label) {
		this.label = label;
	}
}
