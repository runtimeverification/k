package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;

/**
 * Evaluates predicates and functions without doing tree traversal.
 * 
 * @author Traian
 */
public class LocalEvaluator extends LocalTransformer {
    
    /**
     * The symbolic constraint of the {@code ConstrainedTerm} which contains the
     * terms to be evaluated by this evaluator.
     */
    private final SymbolicConstraint constraint;

    public LocalEvaluator(TermContext context) {
        this(null, context);
    }

    public LocalEvaluator(SymbolicConstraint constraint, TermContext context) {
        super(context);
        this.constraint = constraint;
    }
    
    public SymbolicConstraint constraint() {
        return constraint;
    }
    
    @Override
    public ASTNode transform(KItem kItem) {
        return kItem.evaluateFunction(constraint, context);
    }

    @Override
    public ASTNode transform(KItemProjection kItemProjection) {
        return kItemProjection.evaluateProjection();
    }

    @Override
    public ASTNode transform(ListLookup listLookup) {
        return listLookup.evaluateLookup();
    }

    @Override
    public ASTNode transform(SetElementChoice setElementChoice) {
        return setElementChoice.evaluateChoice();
    }

    @Override
    public ASTNode transform(SetLookup setLookup) {
        return setLookup.evaluateLookup();
    }

    @Override
    public ASTNode transform(SetUpdate setUpdate) {
        return setUpdate.evaluateUpdate();
    }

    @Override
    public ASTNode transform(MapKeyChoice mapKeyChoice) {
        return mapKeyChoice.evaluateChoice();
    }

    @Override
    public ASTNode transform(MapLookup mapLookup) {
        return mapLookup.evaluateLookup();
    }

    @Override
    public ASTNode transform(MapUpdate mapUpdate) {
        return mapUpdate.evaluateUpdate();
    }

}
