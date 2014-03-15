package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.*;
import java.util.List;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 11/12/12
 * Time: 10:07 PM
 */
public class ResolveSupercool extends CopyOnWriteTransformer {

    public ResolveSupercool(org.kframework.kil.loader.Context context) {
        super("Cool the <k> cell for supercool rules", context);
    }

    @Override
    public ASTNode transform(Rule node) throws TransformerException {
        for (String cool : kompileOptions.supercool) {
            if (node.containsAttribute(cool)) {
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
            node.setRight(right, context);
        }
        return node;
    }

    @Override
    public ASTNode transform(Cell node) throws TransformerException {
        if (!node.getLabel().equals("k") ) {
            return super.transform(node);
        }
        node = node.shallowCopy();
        if (node.getContents() instanceof KSequence) {
            KSequence kseq = (KSequence) node.getContents().shallowCopy();
            node.setContents(kseq);
            List<Term> kitems = new ArrayList<Term>(kseq.getContents());
            kseq.setContents(kitems);
            kitems.set(0, KApp.of(KLabelConstant.COOL_KLABEL, kitems.get(0)));
        } else {
            KApp kApp = new KApp(KLabelConstant.COOL_KLABEL, node.getContents());
            node.setContents(kApp);
        }
        return node;
    }

    @Override
    public ASTNode transform(Configuration node) throws TransformerException {
        return node;
    }

    @Override
    public ASTNode transform(org.kframework.kil.Context node) throws TransformerException {
        return node;
    }

    @Override
    public ASTNode transform(Syntax node) throws TransformerException {
        return node;
    }
}
