// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.kil.ASTNode;

/**
 * Canonicalizes a term by simplifying its single-element and single-frame
 * {@code Collection}'s.
 *
 * @author YilongL
 *
 */
public class TermCanonicalizer extends CopyOnWriteTransformer {

    public static Term canonicalize(Term term, TermContext context) {
        TermCanonicalizer transformer = new TermCanonicalizer(context);
        return (Term) term.accept(transformer);
    }

    private TermCanonicalizer(TermContext context) {
        super(context);
    }

    @Override
    public ASTNode transform(CellCollection node) {
        Term transformedNode = (Term) super.transform(node);
        if (transformedNode instanceof CellCollection) {
            CellCollection cellCol = (CellCollection) transformedNode;
            if (cellCol.hasFrame() && cellCol.concreteSize() == 0) {
                return cellCol.frame();
            }
        }
        return transformedNode;
    }

    @Override
    public ASTNode transform(KList node) {
        Term transformedNode = KCollection.downKind((Term) super.transform(node));
        if (transformedNode instanceof KList) {
            KList kList = (KList) transformedNode;
            if (kList.hasFrame() && kList.concreteSize() == 0) {
                return kList.frame();
            }
        }
        return transformedNode;
    }

    @Override
    public ASTNode transform(KSequence node) {
        Term transformedNode = KCollection.downKind((Term) super.transform(node));
        if (transformedNode instanceof KSequence) {
            KSequence ksequence = (KSequence) transformedNode;
            if (ksequence.hasFrame() && ksequence.concreteSize() == 0) {
                return ksequence.frame();
            }
        }
        return transformedNode;
    }

    @Override
    public ASTNode transform(BuiltinMap node) {
        if (node.hasFrame() && node.concreteSize() == 0) {
            return node.frame();
        } else {
            return super.transform(node);
        }
    }

    @Override
    public ASTNode transform(BuiltinSet node) {
        if (node.hasFrame() && node.concreteSize() == 0) {
            return node.frame();
        } else {
            return super.transform(node);
        }
    }

    @Override
    public ASTNode transform(BuiltinList node) {
        if (node.hasFrame() && node.concreteSize() == 0) {
            return node.frame();
        } else {
            return super.transform(node);
        }
    }

}
