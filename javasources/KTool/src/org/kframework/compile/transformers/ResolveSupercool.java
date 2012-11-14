package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.general.GlobalSettings;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 11/12/12
 * Time: 10:07 PM
 */
public class ResolveSupercool extends CopyOnWriteTransformer {
    public ResolveSupercool() {
        super("Cool the <k> cell for supercool rules");
    }

    @Override
    public ASTNode transform(Rule node) throws TransformerException {
        final Attributes attributes = node.getAttributes();
        for (String cool : GlobalSettings.supercool) {
            if (attributes.containsKey(cool)) {
                return super.transform(node);
            }
        }
        return node;
    }

    @Override
    public ASTNode transform(Rewrite node) throws TransformerException {
        Term right = (Term)node.getRight().accept(this);
        if (right != node.getRight()) {
            node = node.shallowCopy();
            node.setRight(right);
        }
        return node;
    }

    @Override
    public ASTNode transform(Cell node) throws TransformerException {
        if (node.getLabel().equals("k")) {
            node = node.shallowCopy();
            KApp kApp = new KApp(new Constant("cool", "KLabel"), node.getContents());
            node.setContents(kApp);
            return node;
        }
        return super.transform(node);
    }

    @Override
    public ASTNode transform(Configuration node) throws TransformerException {
        return node;
    }

    @Override
    public ASTNode transform(Context node) throws TransformerException {
        return node;
    }

    @Override
    public ASTNode transform(Syntax node) throws TransformerException {
        return node;
    }
}
