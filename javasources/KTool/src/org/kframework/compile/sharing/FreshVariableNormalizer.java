package org.kframework.compile.sharing;

import org.kframework.kil.Rule;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;


/**
 * Class implementing a transformation which normalizes the fresh variable indices in rules
 * such that if the counting begins at 0 in each rule (i.e., GeneratedFreshVar0 always appears if
 * there is at least one fresh variable in the rule).
 */
public class FreshVariableNormalizer extends CopyOnWriteTransformer {

    private int baseCounter;
    private FreshVariableCounter visitor = new FreshVariableCounter();

    public FreshVariableNormalizer() {
        super("Normalize fresh variable indices");
    }

    @Override
    public Rule transform(Rule rule) {
        baseCounter = Integer.MAX_VALUE;
        rule.accept(visitor);
        if (baseCounter == Integer.MAX_VALUE) {
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
        try {
            if (variable.getName().startsWith("GeneratedFreshVar")) {
                int index = Integer.parseInt(
                        variable.getName().substring("GeneratedFreshVar".length()));
                return new Variable(
                        "GeneratedFreshVar" + (index - baseCounter),
                        variable.getSort());
            }
        } catch (Exception e) { }

        return variable;
    }

    /**
     * Class implementing a visitor which finds the minimum index of a fresh variable.
     */
    class FreshVariableCounter extends BasicVisitor {

        @Override
        public void visit(Variable variable) {
            if (variable.getName().startsWith("GeneratedFreshVar")) {
                try {
                    int index = Integer.parseInt(
                            variable.getName().substring("GeneratedFreshVar".length()));
                    baseCounter = Math.min(baseCounter, index);
                } catch (Exception e) { }
            }
        }

    }

}
