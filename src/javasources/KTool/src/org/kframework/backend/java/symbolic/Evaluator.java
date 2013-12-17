package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;


/**
 * Evaluates predicates and functions in post-order using a copy-on-write
 * strategy.
 * 
 * @author AndreiS
 */
public class Evaluator extends CopyOnWriteTransformer {

    // TODO(YilongL): why not just declare it as a LocalTransformer?
    private final Transformer localEvaluator; // used to perform the actual evaluation

    public Evaluator(TermContext context,Context theContext) {
        super(context);
        localEvaluator = new LocalEvaluator(context,theContext);
    }

    @Override
    public ASTNode transform(KItem kItem) {
        return ((Term) super.transform(kItem)).accept(localEvaluator);
    }

    @Override
    public ASTNode transform(ListLookup listLookup) {
        return ((Term) super.transform(listLookup)).accept(localEvaluator);
    }

    @Override
    public ASTNode transform(MapLookup mapLookup) {
        return ((Term) super.transform(mapLookup)).accept(localEvaluator);
    }

    @Override
    public ASTNode transform(MapUpdate mapUpdate) {
        return ((Term) super.transform(mapUpdate)).accept(localEvaluator);
    }

    @Override
    public ASTNode transform(SetLookup setLookup) {
        return ((Term) super.transform(setLookup)).accept(localEvaluator);
    }

    @Override
    public ASTNode transform(SetUpdate setUpdate) {
        return ((Term) super.transform(setUpdate)).accept(localEvaluator);
    }

}
