// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import java.util.List;

import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.Term;
import org.kframework.kil.Token;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.PrintVisitor;
import org.kframework.utils.StringUtil;

/**
 * Converts from the old KIL hierarchy to the textual KAST.
 * Currently supports the K-SEQ module of KORE only.
 *
 * @author dwightguth
 *
 */
public class KoreFilter extends PrintVisitor {

    public KoreFilter(Context context) {
        super(context);
    }

    @Override
    public Void visit(Token t, StringBuilder sb) {
        sb.append("#token(");
        sb.append(StringUtil.enquoteCString(t.value()));
        sb.append(", \"");
        sb.append(t.tokenSort().toString());
        sb.append("\")");
        return null;
    }

    @Override
    public Void visit(KApp node, StringBuilder sb) throws RuntimeException {
        if (node.getLabel() instanceof Token) {
            return visitNode(node.getLabel(), sb);
        }
        visitNode(node.getLabel(), sb);
        sb.append("(");
        visitNode(node.getChild(), sb);
        sb.append(")");
        return null;
    }

    @Override
    public Void visit(KLabelConstant node, StringBuilder sb)
            throws RuntimeException {
        sb.append(StringUtil.escapeKoreKLabel(node.getLabel()));
        return null;
    }

    @Override
    public Void visit(KList node, StringBuilder sb) throws RuntimeException {
        visitCollection(node.getContents(), ".::KList", ",", sb);
        return null;
    }

    private void visitCollection(List<? extends Term> list, String empty, String delimiter, StringBuilder sb) {
        if (list.size() == 0) {
            sb.append(empty);
            return;
        }
        visitNode(list.get(0), sb);
        for (int i = 1; i < list.size(); i++) {
            sb.append(delimiter);
            visitNode(list.get(i), sb);
        }
    }

    @Override
    public Void visit(KSequence node, StringBuilder sb) throws RuntimeException {
        visitCollection(node.getContents(), ".::K", "~>", sb);
        return null;
    }

}
