// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.ASTNode;

import java.util.Map;
import java.util.Set;


/**
 * Substitutes variables with terms according to a given substitution map.
 * 
 * @author AndreiS
 */
public class SubstitutionTransformer extends PrePostTransformer {

    private final Map<Variable, ? extends Term> substitution;
    
    public SubstitutionTransformer(Map<Variable, ? extends Term> substitution, TermContext context) {
        super(context);
        this.substitution = substitution;
        preTransformer.addTransformer(new LocalVariableChecker());
        postTransformer.addTransformer(new LocalSubstitutionTransformer());
        postTransformer.addTransformer(new VariableUpdaterTransformer());
    }
    
    /**
     * Stops further traversing the term when it contains no variable that needs
     * to be substituted.
     * 
     */
    private class LocalVariableChecker extends LocalTransformer {
        @Override
        public ASTNode transform(JavaSymbolicObject object) {
            // TODO(AndreiS) this stops the traversal for ground terms (even if the functions are not fully evaluated)
            Set<Variable> variables = object.variableSet();
            for (Variable variable : substitution.keySet()) {
                if (variables.contains(variable)) {
                    return object;
                }
            }
            return new DoneTransforming(object);
        }
    }

    /**
     * Local transformer that performs the actual substitution of variables.
     */
    private class LocalSubstitutionTransformer extends LocalTransformer {

        @Override
        public Term transform(Variable variable) {
            Term term = substitution.get(variable);
            if (term != null) {
                return term;
            } else {
                return variable;
            }
        }
    }
   
    /**
     * Recomputes the set of variables contained in each node of the AST.
     * 
     * @author TraianSF
     */
    private class VariableUpdaterTransformer extends LocalTransformer {
        @Override
        protected ASTNode transform(JavaSymbolicObject object) {
            object.updateVariableSet();
            return object;
        }
    }
}
