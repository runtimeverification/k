package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.List;

import org.kframework.backend.java.kil.TermFormulaPair;
import org.kframework.kil.ASTNode;

/**
 * Collects symbolic constraints generated during evaluation of
 * functions/predicates.
 * 
 * @author YilongL
 * 
 */
public class LocalConstraintCollector extends LocalTransformer {

    private final List<UninterpretedConstraint> multiConstraints;
    
    public LocalConstraintCollector(List<UninterpretedConstraint> multiConstraints) {
        this.multiConstraints = multiConstraints;
    }

    // TODO(YilongL): consider including this method into the Transformer interface 
    public ASTNode transform(TermFormulaPair pair) {
        List<UninterpretedConstraint> tmpMultiConstraints = new ArrayList<UninterpretedConstraint>(
                multiConstraints);
        multiConstraints.clear();
        
        /* compute Cartesian product of two disjunctions of conjunctions */
        for (UninterpretedConstraint c1 : tmpMultiConstraints) {
            for (UninterpretedConstraint c2 : pair.multiConstraints()) {
                UninterpretedConstraint newCnstr = new UninterpretedConstraint();
                newCnstr.addAll(c1);
                newCnstr.addAll(c2);
                multiConstraints.add(newCnstr);
            }
        }
        return pair.term();
    }
}
