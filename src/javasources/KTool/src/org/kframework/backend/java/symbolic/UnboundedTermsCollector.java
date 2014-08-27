// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.common.collect.HashMultiset;
import com.google.common.collect.Multimap;
import com.google.common.collect.Multiset;
import org.kframework.backend.java.kil.*;

import java.util.HashSet;
import java.util.Set;

/**
 * Collects all terms which are not bound by a binder.
 * In some sense it is similar to computing the free variables
 * However since we don't know for sure what can be bound and what not
 * we simply remove the bound terms from all the others.
 *
 * @author TraianSF
 */
public class UnboundedTermsCollector extends PrePostVisitor {
    Multiset<Term> boundVariables;
    Set<Term> unboundedTerms;

    /**
     * Computes unbounded terms of a given term
     * @param term --- the term to compute the set of unbounded terms for
     * @return the set of unbounded terms in {@code term}
     */
    public static Set<Term> getUnboundedTerms(Term term) {
        UnboundedTermsCollector collector = new UnboundedTermsCollector();
        term.accept(collector);
        return collector.unboundedTerms;
    }

    private UnboundedTermsCollector() {
        boundVariables = HashMultiset.create();
        unboundedTerms = new HashSet<>();
        preVisitor.addVisitor(new LocalVisitor() {
            @Override
            public void visit(KItem kItem) {
                handleBinderVariables(kItem, true);
            }
        });
        postVisitor.addVisitor(new LocalVisitor() {
            @Override
            public void visit(KItem kItem) {
                handleBinderVariables(kItem, false);
            }
        });
        preVisitor.addVisitor(new LocalVisitor(){
            @Override
            public void visit(Term node) {
                if (! boundVariables.contains(node)) {
                    unboundedTerms.add(node);
                }
                super.visit(node);
            }
        });
     }

    private void handleBinderVariables(KItem kItem, boolean add) {
        // TODO(AndreiS): fix binder when dealing with KLabel variables and non-concrete KLists
        if (!(kItem.kLabel() instanceof KLabel) || !(kItem.kList() instanceof KList)) {
            return;
        }

        KLabel kLabel = (KLabel) kItem.kLabel();
        KList kList = (KList) kItem.kList();
        if (kLabel instanceof KLabelConstant) {
            KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
            if (kLabelConstant.isBinder()) {  // if label is a binder rename all bound variables
                Multimap<Integer, Integer> binderMap = kLabelConstant.getBinderMap();
                for (Integer keyIndex : binderMap.keySet()) {
                    if (add) {
                        boundVariables.add(kList.get(keyIndex));
                    } else {
                        boundVariables.remove(kList.get(keyIndex));
                    }
                }
            }
        }
    }


}
