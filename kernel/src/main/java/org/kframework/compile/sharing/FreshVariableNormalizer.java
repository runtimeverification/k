// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.compile.sharing;

import static org.kframework.kil.Variable.GENERATED_ANON_VAR;

import org.kframework.kil.Rule;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.NonCachingVisitor;

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
    public Rule visit(Rule rule, Void _void) {
        counter = 0;
        substitution.clear();
        visitor.visitNode(rule);
        if (substitution.isEmpty()) {
            // no fresh variables in this rule
            return rule;
        }

        return (Rule) super.visit(rule, _void);
    }

    @Override
    public Variable visit(Variable variable, Void _void) {
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
    public class FreshVariableCounter extends NonCachingVisitor {

        public FreshVariableCounter(Context context) {
            super(context);
        }

        @Override
        public Void visit(Variable variable, Void _void) {
            if (substitution.containsKey(variable)) {
                return null;
            }

            if (variable.getName().startsWith(GENERATED_ANON_VAR)) {
                try {
                    Integer.parseInt(variable.getName().substring(GENERATED_ANON_VAR.length()));
                    substitution.put(
                            variable,
                            new Variable("_" + counter++, variable.getSort()));
                } catch (NumberFormatException e) { }
            }

            if (variable.getName().matches("_\\d+")) {
                try {
                    Integer.parseInt(variable.getName().substring(1));
                    substitution.put(
                            variable,
                            new Variable("_" + counter++, variable.getSort()));
                } catch (NumberFormatException e) { }
            }

            return null;
        }

    }

}
