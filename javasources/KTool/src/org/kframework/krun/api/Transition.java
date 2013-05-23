package org.kframework.krun.api;

import java.io.Serializable;

import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.kil.loader.Context;
import org.kframework.krun.K;

/**
A transitition in the transition system of a semantics. Used to represent edges in the search graph
associated with breadth-first search, LTL model-checking, and debugging.
*/
public class Transition implements Serializable{

	/**
	The rule transforming the origin state to the destination state
	*/
	private ASTNode rule;

	/**
	The label of the rule transforming the origin state to the destination state, if the entire rule
	is unavailable
	*/
	private String label;

	private TransitionType type;

	protected Context context;

	public Transition(ASTNode rule, Context context) {
		this.context = context;
		this.rule = rule;
		this.type = TransitionType.RULE;
	}

	public Transition(String label, Context context) {
		this.context = context;
		this.label = label;
		this.type = TransitionType.LABEL;
	}

	public Transition(TransitionType type, Context context) {
		this.context = context;
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
		/**
		A transition for which the rule transforming the origin to the destination is known
		*/
		RULE,
		/**
		A transition for which only the rule label of the underlying rule is known.
		*/
		LABEL,
		/**
		A transition for which no further information is available, except that the rule had no
		label.
		*/
		UNLABELLED,
		/**
		A rewrite or set of rewrites containing no transitions.
		*/
		REDUCE
	}

	public TransitionType getType() {
		return type;
	}

	@Override
	public String toString() {
		if (rule != null) {
			Attributes a = rule.getAttributes();
			UnparserFilter unparser = new UnparserFilter(true, K.color, K.parens, context);
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
