package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;

/**
 * Evaluates predicates and functions without doing tree traversal.
 * 
 * @author Traian
 */
public class LocalEvaluator extends LocalTransformer {

    protected final Context theContext;

    public LocalEvaluator(TermContext context,Context theContext) {
        super(context);
    	this.theContext=theContext;

    }

    @Override
    public ASTNode transform(KItem kItem) {
        return kItem.evaluateFunction(context,this.theContext);
    }

    @Override
    public ASTNode transform(ListLookup listLookup) {
        return listLookup.evaluateLookup();
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
    public ASTNode transform(MapLookup mapLookup) {
        return mapLookup.evaluateLookup();
    }

    @Override
    public ASTNode transform(MapUpdate mapUpdate) {
        return mapUpdate.evaluateUpdate();
    }

}
