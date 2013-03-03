package org.kframework.krun.api;

import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.krun.K;

public class Transition {

	private ASTNode rule;
	private String label;
	private TransitionType type;

	public Transition(ASTNode rule) {
		this.rule = rule;
		this.type = TransitionType.RULE;
	}

	public Transition(String label) {
		this.label = label;
		this.type = TransitionType.LABEL;
	}

	public Transition(TransitionType type) {
		if (type == TransitionType.RULE || type == TransitionType.LABEL) {
			throw new RuntimeException("Must specify argument for transition types RULE and LABEL");
		}
		this.type = type;
	}

	public ASTNode getRule() {
		return rule;
	}

	public void setRule(ASTNode rule) {
		this.rule = rule;
	}

	public String getLabel() {
		return label;
	}

	public void setLabel(String label) {
		this.label = label;
	}

	public enum TransitionType {
		RULE,
		LABEL,
		UNLABELLED,
		REDUCE
	}

	public TransitionType getType() {
		return type;
	}

	@Override
	public String toString() {
		if (rule != null) {
			Attributes a = rule.getAttributes();
			UnparserFilter unparser = new UnparserFilter(true, K.color, K.parens);
			a.accept(unparser);
			return "\nRule tagged " + unparser.getResult() + " ";
		} else if (label != null) {
			return "\nRule labelled " + label + " ";
		} else if (type == TransitionType.REDUCE) {
			return "\nMaude 'reduce' command ";
		} else {
			return "\nUnlabelled rule ";
		}
	}
}
