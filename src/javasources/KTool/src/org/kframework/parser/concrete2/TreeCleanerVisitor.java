package org.kframework.parser.concrete2;

import org.kframework.backend.java.symbolic.CopyOnWriteTransformer;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.GenericToken;
import org.kframework.kil.KApp;
import org.kframework.kil.KList;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.Iterator;

/**
 * Remove parsing artifacts like #token("#$DeleteSort$#", "")() generated
 * from epsilon states and reduces the
 */
public class TreeCleanerVisitor extends BasicTransformer {
    public TreeCleanerVisitor(Context context) {
        super(TreeCleanerVisitor.class.getName(), context);
    }
    // It might be just a temporary solution. Mark kapps and #tokens in nodes
    // produced by the parser with this sort, in order to delete them after
    // the tree has been completely constructed.
    public static final String DELETESORT = "#$DeleteSort$#";

    @Override
    public ASTNode transform(Ambiguity node) throws TransformerException {
        if (node.getContents().size() == 1)
            return node.getContents().get(0).accept(this);
        else
            return super.transform(node);
    }

    @Override
    public ASTNode transform(KApp node) throws TransformerException {
        KList children = (KList) node.getChild();
        Iterator<Term> iter = children.getContents().iterator();
        while (iter.hasNext()) {
            Term trm = iter.next();
            if (trm instanceof KApp) {
                KApp child = (KApp) trm;
                if (child.getLabel() instanceof GenericToken) {
                    GenericToken gt = (GenericToken) child.getLabel();
                    if (gt.tokenSort().equals(DELETESORT)) {
                        iter.remove();
                    }
                }
            }
        }
        return super.transform(node);
    }
}
