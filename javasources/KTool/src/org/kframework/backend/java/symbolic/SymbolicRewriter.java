package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.kframework.backend.symbolic.SymbolicBackend;
import org.kframework.kil.Attribute;
import org.kframework.kil.Definition;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.exceptions.TransformerException;


/**
 * Created with IntelliJ IDEA. User: andrei Date: 3/12/13 Time: 4:03 PM To change this template use File | Settings | File Templates.
 */
public class SymbolicRewriter {

    private final List<Rule> rules;
	private final SymbolicMatcher matcher;
    private final Transformer transformer;


	public SymbolicRewriter(Definition definition) {
		matcher = new SymbolicMatcher();
        transformer = new KILtoBackendJavaKILTransformer();

        rules = new ArrayList<Rule>(definition.getSingletonModule().getRules().size());
        for (org.kframework.kil.Rule rule : definition.getSingletonModule().getRules()) {
			if (!rule.containsAttribute(SymbolicBackend.SYMBOLIC)
                    || rule.containsAttribute(Attribute.FUNCTION.getKey())
                    || rule.containsAttribute(Attribute.PREDICATE.getKey())
					|| rule.containsAttribute(Attribute.ANYWHERE.getKey())) {
				continue;
			}

            try {
                rules.add((Rule) rule.accept(transformer));
            } catch (TransformerException e) {
                e.printStackTrace();
            }
        }
	}

	public org.kframework.kil.Term rewrite(org.kframework.kil.Term kilTerm) {
        Term term;
        try {
            term = (Term) kilTerm.accept(transformer);
        } catch (TransformerException e) {
            e.printStackTrace();
            return null;
        }

        for (Rule rule : rules) {
			if (matcher.isMatching(term, rule.getLeftHandSide())) {
                Map<Variable, Term> substitution = new HashMap<Variable, Term>();
                for (SymbolicEquality symbolicEquality : matcher.getConstraints()) {
                    if (symbolicEquality.rhs instanceof Variable) {
                        substitution.put((Variable) symbolicEquality.rhs, symbolicEquality.lhs);
                    }
                }

                System.err.println(rule.getLeftHandSide());
                System.err.println(rule.getLeftHandSide().variableSet());
                System.err.println(matcher.getConstraints());
                System.err.println(rule.getRightHandSide().substitute(substitution));
			}
		}

		return kilTerm;
	}

}
