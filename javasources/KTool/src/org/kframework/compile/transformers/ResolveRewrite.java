package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Initially created by: Traian Florin Serbanuta
 * Date: 11/1/12
 * Time: 7:59 AM
 */
public class ResolveRewrite extends CopyOnWriteTransformer {

    public ResolveRewrite() {
        super("Pushing local rewrites to top");
    }

    @Override
    public ASTNode transform(Rule node) throws TransformerException {
        Term body = node.getBody();
        if (body instanceof Rewrite) return node;
        node = node.shallowCopy();
        Term left = (Term) body.accept(new OneSideTransformer(LRHS.LEFT));
        Term right = (Term) body.accept(new OneSideTransformer(LRHS.RIGHT));
        Rewrite rewrite = new Rewrite(left, right);
        node.setBody(rewrite);
        return node;
    }

    @Override
    public ASTNode transform(Syntax node) throws TransformerException {
        return node;
    }

    @Override
    public ASTNode transform(Configuration node) throws TransformerException {
        return node;
    }

    @Override
    public ASTNode transform(Context node) throws TransformerException {
        return node;    //To change body of overridden methods use File | Settings | File Templates.
    }

    public enum LRHS {
        LEFT,
        RIGHT,
    }

    public class OneSideTransformer extends CopyOnWriteTransformer {
        private LRHS lrhs;

        public OneSideTransformer(LRHS lrhs) {
            super("Retrieving the " + lrhs + "side of the term");
            this.lrhs = lrhs;
        }

        @Override
        public ASTNode transform(Rewrite node) throws TransformerException {
            switch (lrhs) {
                case LEFT:
                    return node.getLeft();
                case RIGHT:
                    return node.getRight();
            }
            return null;
        }
    }
}
