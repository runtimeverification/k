package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.KItem;
import org.kframework.kil.ASTNode;


/**
 * @author: AndreiS
 */
public class FunctionEvaluator extends CopyOnWriteTransformer {

    @Override
    public ASTNode transform(KItem kItem) {
        return kItem.evaluateFunction();
    }

}
