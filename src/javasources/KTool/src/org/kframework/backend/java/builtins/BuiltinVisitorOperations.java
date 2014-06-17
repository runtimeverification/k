// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.symbolic.LocalTransformer;
import org.kframework.backend.java.symbolic.PrePostTransformer;
import org.kframework.kil.ASTNode;

import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.ImmutableList;


/**
 * Provides a builtin implementation of a K visitor.
 *
 * @see include/modules/k-functional-visitor.k
 *
 * @author Traian
 */
public class BuiltinVisitorOperations extends PrePostTransformer {

    /**
     * KLabel of the guard controlling whether a node is visited.
     */
    private final KLabel ifLabel;
    /**
     * List of arguments passed to the guard KLabel.
     */
    private final List<Term> ifParams;
    /**
     * KLabel of the visitation performed on a node.
     */
    private final KLabel visitLabel;
    /**
     * List of arguments passed the visitation KLabel.
     */
    private final List<Term> visitParams;

    BuiltinVisitorOperations(
            KLabel ifLabel,
            List<Term> ifParams,
            KLabel visitLabel,
            List<Term> visitParams,
            TermContext context) {
        super(context);
        this.ifLabel = ifLabel;
        this.ifParams = ifParams;
        this.visitLabel = visitLabel;
        this.visitParams = visitParams;

        preTransformer.addTransformer(new LocalTransformer(context) {
            @Override
            public ASTNode transform(Term term) {
                if (term instanceof KLabel) {
                    return new DoneTransforming(term);
                }

                if (evaluateGuard(term)) {
                    return new DoneTransforming(visitNode(term));
                } else {
                    return term;
                }
            }
        });
    }

    private Term visitNode(Term term) {
        visitParams.set(0, term);
        term = new KItem(
                visitLabel,
                new KList(visitParams),
                context);
        return term.evaluate(context);
    }

    private boolean evaluateGuard(Term term) {
        ifParams.set(0, term);
        KItem test = new KItem(
                ifLabel,
                new KList(ifParams),
                context);
        // TODO: Think about what happens when test has symbolic values in it.
        return test.evaluate(context) == BoolToken.TRUE;
    }

    private static Term getInjectedTerm(KItem kItem) {
        return ((KLabelInjection) kItem.kLabel()).term();
    }

    /**
     * Implements operation {@code #visit(K, VisitLabel, VisitList, IfLabel, IfList)}.
     *
     * @param term Term being visited
     * @param visitLabelTerm {@code KItem} representation of the kLabel of the visitation performed on a node
     * @param visitListTerm {@code KItem} representation of the kList of additional arguments passed the visitation KLabel
     * @param ifLabelTerm {@code KItem} representation of the kLabel of the guard controlling whether a node is visited
     * @param ifListTerm {@code KItem} representation of the kList of additional arguments passed to the guard KLabel
     * @param context
     * @return Visited term
     *
     * @see org.kframework.backend.java.kil.KLabelInjection
     */
    public static Term visit(
            Term term,
            KItem visitLabelTerm,
            KItem visitListTerm,
            KItem ifLabelTerm,
            KItem ifListTerm,
            TermContext context) {
        KLabel visitLabel;
        KList visitList;
        KLabel ifLabel;
        KList ifList;
        try {
            visitLabel = (KLabel) getInjectedTerm(visitLabelTerm);
            visitList = (KList) KCollection.upKind(getInjectedTerm(visitListTerm), Kind.KLIST);
            ifLabel = (KLabel) getInjectedTerm(ifLabelTerm);
            ifList = (KList) KCollection.upKind(getInjectedTerm(ifListTerm), Kind.KLIST);
        } catch (ClassCastException e) {
            throw new IllegalArgumentException(e);
        }
        final ArrayList<Term> ifParams = new ArrayList<>();
        ifParams.add(term);
        ifParams.addAll(ifList.getContents());
        final ArrayList<Term> visitParams = new ArrayList<>();
        visitParams.add(term);
        visitParams.addAll(visitList.getContents());
        return (Term) term.accept(
                new BuiltinVisitorOperations(ifLabel, ifParams, visitLabel, visitParams, context));
    }

}
