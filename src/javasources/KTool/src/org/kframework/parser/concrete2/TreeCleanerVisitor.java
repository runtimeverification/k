// Copyright (C) 2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete2;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.KApp;
import org.kframework.kil.KList;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Remove parsing artifacts such as single element ambiguities.
 */
// TODO: simplify by removing left over "null" checks and recheck this code
public class TreeCleanerVisitor extends BasicTransformer {
    public TreeCleanerVisitor(Context context) {
        super(TreeCleanerVisitor.class.getName(), context);
    }

    @Override
    public ASTNode transform(Ambiguity node) throws TransformerException {
        java.util.List<Term> contents = new ArrayList<>();
        for (Term t : node.getContents()) {
            ASTNode transformed = t.accept(this);
            if (transformed != null)
                contents.add((Term) transformed);
        }
        node.setContents(contents);
        if (contents.size() == 0)
            return null;
        else if(contents.size() == 1)
            return contents.get(0);
        else
            return node;
    }

    @Override
    public ASTNode transform(KApp node) throws TransformerException {
        ASTNode rez = node.getChild().accept(this);
        if (rez == null)
            node.setChild(KList.EMPTY);
        else if (rez instanceof KList)
            node.setChild((KList) rez);
        else {
            KList contents = new KList();
            contents.getContents().add((Term) rez);
            node.setChild(contents);
        }
        return node;
    }

    @Override
    public ASTNode transform(KList node) throws TransformerException {
        java.util.List<Term> contents = new ArrayList<>();
        for (Term t : node.getContents()) {
            ASTNode transformed = t.accept(this);
            if (transformed != null)
                contents.add((Term) transformed);
        }
        node.setContents(contents);
        if (contents.size() == 0)
            return null;
        else if(contents.size() == 1)
            return contents.get(0);
        else
            return node;
    }
}
