// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

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
    public ASTNode visit(Rule node, Void _)  {
        for (String cool : kompileOptions.supercool) {
            if (node.containsAttribute(cool)) {
                return super.visit(node, _);
            }
        }
        return node;
    }

    @Override
    public ASTNode visit(Rewrite node, Void _)  {
        Term right = (Term) this.visitNode(node.getRight());
        if (right != node.getRight()) {
            node = node.shallowCopy();
            node.setRight(right, context);
        }
        return node;
    }

    @Override
    public ASTNode visit(Cell node, Void _)  {
        if (!node.getLabel().equals("k") ) {
            return super.visit(node, _);
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
    public ASTNode visit(Configuration node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(org.kframework.kil.Context node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(Syntax node, Void _)  {
        return node;
    }
}
