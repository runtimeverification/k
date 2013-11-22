package org.kframework.backend.symbolic;

import org.kframework.kil.ASTNode;
import org.kframework.kil.KSequence;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Created with IntelliJ IDEA.
 * User: andrei.arusoaie
 * Date: 11/21/13
 * Time: 10:58 AM
 * If node is $PGM ~> GeneratedFreshVariable then it returns $PGM
 */
public class RemoveExtraVariable extends CopyOnWriteTransformer {
    public RemoveExtraVariable(Context context) {
        super("Removes variable added by ResolveOpenCells", context);
    }

    @Override
    public ASTNode transform(KSequence node) throws TransformerException {
        return node.getContents().get(0);
    }
}
