package org.kframework.backend.symbolic;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Replace variables which appear more than twice with
 * new variables and store them in a map.
 *
 * @author andreiarusoaie
 */
public class VariableReplaceTransformer extends CopyOnWriteTransformer {

    private Map<Variable, Variable> generatedVariables;
    private Set<String> vars;

    public VariableReplaceTransformer(String name, Context context) {
        super("Replace Variables", context);
        generatedVariables = new HashMap<Variable, Variable>();
        vars = new HashSet<String>();
    }

    @Override
    public ASTNode transform(Variable node) throws TransformerException {
        if (MetaK.isBuiltinSort(node.getSort()))
            return node;

        Variable newVar = node;
        if (vars.contains(node.getName()) && !node.isFresh()) {
            newVar = Variable.getFreshVar(node.getSort());
            generatedVariables.put(node, newVar);
        }

        vars.add(node.getName());
        return newVar;
    }

    public Map<Variable, Variable> getGeneratedVariables() {
        return generatedVariables;
    }
}
