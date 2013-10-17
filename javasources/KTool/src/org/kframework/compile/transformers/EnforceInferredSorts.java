package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Syntax;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Created with IntelliJ IDEA.
 * User: traiansf
 * Date: 10/16/13
 * Time: 11:52 PM
 * To change this template use File | Settings | File Templates.
 */
public class EnforceInferredSorts extends CopyOnWriteTransformer {
    public EnforceInferredSorts(Context context1) {
        super("Setting inferred sorts as the default.", context1);
    }

    @Override
    public ASTNode transform(Syntax node) throws TransformerException {
        return node;
    }

    @Override
    public ASTNode transform(Variable node) throws TransformerException {
        if (!node.isUserTyped()) {
            if (node.getExpectedSort() != null) {
                Variable result = node.shallowCopy();
                result.setSort(result.getExpectedSort());
                node = result;
            }
        }
        return node;
    }
}
