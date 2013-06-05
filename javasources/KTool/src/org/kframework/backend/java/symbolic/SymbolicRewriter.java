package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.loader.Context;

import java.util.Map;


/**
 *
 *
 * @author AndreiS
 */
public class SymbolicRewriter {

    private final Context context;
    private final Definition definition;
	private final SymbolicMatcher matcher;

	public SymbolicRewriter(Definition definition, Context context) {
        this.definition = definition;
        this.context = context;
		matcher = new SymbolicMatcher(context);
	}

	public Term rewrite(Term term) {
        for (Rule rule : definition.rules()) {
			if (matcher.isMatching(term, rule.getLeftHandSide())) {
                Map<Variable, Term> freshSubstitution
                        = matcher.constraint().freshSubstitution(rule.variableSet());
                Term result = rule.getRightHandSide()
                        .substitute(matcher.constraint().substitution(), context)
                        .substitute(freshSubstitution, context);

                System.err.println(rule.getLeftHandSide());
                System.err.println(matcher.constraint());
                System.err.println(result);

                /* return first match */
                return result;
			}
		}

		return null;
	}

    public Term rewriteStar(Term term) {
        Term oldTerm;

        do {
            oldTerm = term;
            term = rewrite(term);
        } while (term != null);

        return oldTerm;
    }

}
