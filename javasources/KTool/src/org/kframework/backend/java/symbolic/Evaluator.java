package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;


/**
 * @author AndreiS
 */
public class Evaluator extends CopyOnWriteTransformer {

    private final Transformer localEvaluator;

    public Evaluator(TermContext context) {
        super(context);
        localEvaluator = new LocalEvaluator(context);
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
    public ASTNode transform(ListUpdate listUpdate) {
        return ((Term) super.transform(listUpdate)).accept(localEvaluator);
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
