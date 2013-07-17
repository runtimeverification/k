package org.kframework.compile.sharing;

import org.kframework.kil.Rule;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.HashMap;
import java.util.Map;


/**
 * Class implementing a transformation which normalizes the fresh variable indices in rules
 * such that the occurring indices are precisely the numbers in some interval [0, n].
 */
public class FreshVariableNormalizer extends CopyOnWriteTransformer {

    private int counter;
    private Map<Variable, Variable> substitution = new HashMap<Variable, Variable>();
    private FreshVariableCounter visitor;

    public FreshVariableNormalizer(Context context) {
        super("Normalize fresh variable indices", context);
        visitor = new FreshVariableCounter(context);
    }

    @Override
    public Rule transform(Rule rule) {
        counter = 0;
        substitution.clear();
        rule.accept(visitor);
        if (substitution.isEmpty()) {
            // no fresh variables in this rule
            return rule;
        }

        try {
            return (Rule) super.transform(rule);
        } catch (TransformerException e) {
            return rule;
        }
    }

    @Override
    public Variable transform(Variable variable) {
        Variable substituteVariable = substitution.get(variable);
        if (substituteVariable != null) {
            return substituteVariable;
        } else {
            return variable;
        }
    }

    /**
     * Class implementing a visitor which constructs a substitution mapping the fresh variables
     * into variables with indices the number in the range [0, this.counter].
     */
    class FreshVariableCounter extends BasicVisitor {

        public FreshVariableCounter(Context context) {
			super(context);
		}

		@Override
        public void visit(Variable variable) {
            if (substitution.containsKey(variable)) {
                return;
            }

            if (variable.getName().startsWith("GeneratedFreshVar")) {
                try {
                    Integer.parseInt(variable.getName().substring("GeneratedFreshVar".length()));
                    substitution.put(
                            variable,
                            new Variable("GeneratedFreshVar" + counter++, variable.getSort()));
                } catch (Exception e) { }
            }
        }

    }

}
