// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete2;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.KApp;
import org.kframework.kil.KList;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.kil.visitors.exceptions.ParseFailedException;

/**
 * Remove parsing artifacts such as single element ambiguities.
 */
// TODO: simplify by removing left over "null" checks and recheck this code
public class TreeCleanerVisitor extends ParseForestTransformer {
    public TreeCleanerVisitor(Context context) {
        super(TreeCleanerVisitor.class.getName(), context);
    }

    @Override
    public ASTNode visit(KApp node, Void _) throws ParseFailedException {
        ASTNode rez = this.visitNode(node.getChild());
        assert rez != null;
        if (rez instanceof KList)
            node.setChild((KList) rez);
        else {
            KList contents = new KList();
            contents.getContents().add((Term) rez);
            node.setChild(contents);
        }
        return node;
    }

    @Override
    public ASTNode visit(KList node, Void _) throws ParseFailedException {
        java.util.List<Term> contents = new ArrayList<>();
        for (Term t : node.getContents()) {
            ASTNode transformed = this.visitNode(t);
            if (transformed != null)
                contents.add((Term) transformed);
        }
        node.setContents(contents);
        if (contents.size() == 0)
            return KList.EMPTY;
        else if(contents.size() == 1)
            return contents.get(0);
        else
            return node;
    }
}
