package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;


/**
 * Transformer class compiling map accesses into load and store operations.
 *
 * @author AndreiS
 */
public class MapToLoadStore extends CopyOnWriteTransformer {

    private enum Status {LHS, RHS, CONDITION };

    private Status status;

    public MapToLoadStore(Context context) {
        super("Compile maps into load and store operations", context);
    }

    @Override
    public ASTNode transform(Rule node) throws TransformerException {
        assert node.getBody() instanceof Rewrite:
               "expected rewrite at the top of rule " + node + ". "
               + "MapToLoadStore pass should be applied after ResolveRewrite pass";

        Rewrite rewrite = (Rewrite) node.getBody();
        status = Status.LHS;
        Term lhs = (Term) rewrite.getLeft().accept(this);
        status = Status.RHS;
        Term rhs = (Term) rewrite.getRight().accept(this);
        Term condition = node.getCondition();
        if (condition != null) {
            status = Status.CONDITION;
            condition = (Term) condition.accept(this);
        }

        if (lhs == rewrite.getLeft()
                && rhs == rewrite.getRight()
                && condition == node.getCondition()) {
            return node;
        }

        Rule returnNode = node.shallowCopy();
        rewrite = rewrite.shallowCopy();
        rewrite.setLeft(lhs, context);
        rewrite.setRight(rhs, context);
        returnNode.setBody(rewrite);
        returnNode.setCondition(condition);
        return returnNode;
    }

    @Override
    public ASTNode transform(MapBuiltin node) {
        return node;
    }

}
