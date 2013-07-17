package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;


/**
 * @author: AndreiS
 */
public class Evaluator extends CopyOnWriteTransformer {

    private class LocalEvaluator extends CopyOnWriteTransformer {

        public LocalEvaluator(Context context) {
            super(context);
        }

        @Override
        public ASTNode transform(KItem kItem) {
            return kItem.evaluateFunction();
        }

        @Override
        public ASTNode transform(SetLookup setLookup) {
            return setLookup.evaluateLookup();
        }

        @Override
        public ASTNode transform(SetUpdate mapUpdate) {
            return mapUpdate.evaluateUpdate();
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

    private final Transformer localEvaluator;

    public Evaluator(Context context) {
        super(context);
        localEvaluator = new LocalEvaluator(context);
    }

    @Override
    public ASTNode transform(KItem kItem) {
        return ((Term) super.transform(kItem)).accept(localEvaluator);
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
