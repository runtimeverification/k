// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class FlattenDisambiguationFilter extends CopyOnWriteTransformer {
    public FlattenDisambiguationFilter(Context context) {
        super("Reflatten ambiguous syntax", context);
    }

    @Override
    public ASTNode visit(Ambiguity amb, Void _)  {

        if (amb.getContents().get(0) instanceof TermCons) {
            TermCons t1 = (TermCons)amb.getContents().get(0);
            if (t1.getSort().isComputationSort()) {
                if (t1.getProduction().isListDecl()) {
                    Term t2 = t1.getContents().get(1);
                    UserList ul = (UserList)t1.getProduction().getItems().get(0);
                    if (context.isSubsortedEq(ul.getSort(), t2.getSort())) {
                        t1.getContents().set(1, addEmpty(t2, t1.getSort()));
                    }
                    if (t2 instanceof ListTerminator) {
                        t1.getContents().set(1, new ListTerminator(ul.getSeparator()));
                    }
                }
                return new KApp(
                        KLabelConstant.of(t1.getProduction().getKLabel(), context),
                        (Term) this.visitNode(new KList(t1.getContents())));
            }
        } else if (amb.getContents().get(0) instanceof ListTerminator) {
            ListTerminator t1 = (ListTerminator)amb.getContents().get(0);
            if (t1.getSort().isComputationSort()) {
                return new ListTerminator(((UserList) context.listProductions.get(t1.getSort()).getItems().get(0)).getSeparator());
            }
        }
        return amb;
    }

    private Term addEmpty(Term node, Sort sort) {
        TermCons tc = new TermCons(sort, context.listProductions.get(sort));
        List<Term> contents = new ArrayList<Term>();
        contents.add(node);
        contents.add(new ListTerminator(sort, null));
        tc.setContents(contents);
        return tc;
    }
}
