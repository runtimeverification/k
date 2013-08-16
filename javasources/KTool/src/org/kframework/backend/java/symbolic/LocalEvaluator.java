package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;

/**
* @author Traian
*/
public class LocalEvaluator extends LocalTransformer {

    public LocalEvaluator(TermContext context) {
        super(context);
    }

    @Override
    public ASTNode transform(KItem kItem) {
        return kItem.evaluateFunction(context);
    }

    @Override
    public ASTNode transform(ListLookup listLookup) {
        return listLookup.evaluateLookup();
    }

//    @Override
//    public ASTNode transform(ListUpdate listUpdate) {
//        return listUpdate.evaluateUpdate();
//    }

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
