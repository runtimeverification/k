package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.symbolic.SymbolicBackend;
import org.kframework.kil.Attribute;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.exceptions.TransformerException;


/**
 * Created with IntelliJ IDEA. User: andrei Date: 3/12/13 Time: 4:03 PM To change this template use File | Settings | File Templates.
 */
public class SymbolicRewriter {

    private final List<Rule> rules;
	private final SymbolicMatcher matcher;
    private final Transformer transformer;
    protected DefinitionHelper definitionHelper;

	public SymbolicRewriter(Definition definition, DefinitionHelper definitionHelper) {
		this.definitionHelper = definitionHelper;
		matcher = new SymbolicMatcher(definitionHelper);
        transformer = new KILtoBackendJavaKILTransformer(definitionHelper);

        rules = new ArrayList<Rule>(definition.getSingletonModule().getRules().size());
        for (org.kframework.kil.Rule kilRule : definition.getSingletonModule().getRules()) {
			if (!kilRule.containsAttribute(SymbolicBackend.SYMBOLIC)
                    || kilRule.containsAttribute(Attribute.FUNCTION.getKey())
                    || kilRule.containsAttribute(Attribute.PREDICATE.getKey())
					|| kilRule.containsAttribute(Attribute.ANYWHERE.getKey())) {
				continue;
			}

            Rule rule = null;
            try {
                //System.err.println(kilRule);
                //System.err.flush();
                rule = (Rule) kilRule.accept(transformer);
            } catch (TransformerException e) {
                System.err.println(kilRule);
                System.err.flush();
                e.printStackTrace();
            }
            if (rule != null) {
                //System.err.println(rule);
                rules.add(rule);
            }
        }
	}

	public Term rewrite(Term term) {
        for (Rule rule : rules) {
			if (matcher.isMatching(term, rule.getLeftHandSide())) {
                Map<Variable, Term> freshSubstitution = matcher.getConstraint().freshSubstitution(rule.variableSet());
                Map<Variable, Term> substitution = matcher.getConstraint().getSubstitution();


                System.err.println(rule.getLeftHandSide());
                System.err.println(matcher.getConstraint());
                System.err.println(rule.getRightHandSide().substitute(substitution, definitionHelper).substitute(freshSubstitution, definitionHelper));

                // return first match
                return rule.getRightHandSide().substitute(substitution, definitionHelper).substitute(freshSubstitution, definitionHelper);
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
