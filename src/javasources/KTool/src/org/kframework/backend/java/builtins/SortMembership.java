package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Token;
import org.kframework.kil.loader.Context;

import com.google.common.collect.ImmutableSet;

/**
 * Utility class for checking sort membership predicates.
 * 
 * @author AndreiS
 */
public class SortMembership {

    /**
     * Evaluates a sort membership predicate with respect to a given
     * {@link org.kframework.kil.loader.Context}.
     * 
     * @param kItem
     *            the sort membership predicate
     * @param context
     *            the context
     * @return {@link BoolToken#TRUE} if the predicate is true; or
     *         {@link BoolToken#FALSE} if the predicate is false; otherwise, the
     *         {@code kItem} itself if the evaluation gets stuck
     */
    public static Term check(KItem kItem, Context context) {
        assert kItem.kLabel() instanceof KLabelConstant;
        assert kItem.kList() instanceof KList
                && ((KList) kItem.kList()).size() == 1
                && !((KList) kItem.kList()).hasFrame();

        String predicateSort = ((KLabelConstant) kItem.kLabel()).label().substring("is".length());
        if (!context.getAllSorts().contains(predicateSort)) {
            return kItem;
        }

        Term term = ((KList) kItem.kList()).getContents().get(0);
        String termSort = term.sort();
        if (term.isExactSort()) {
            return context.isSubsortedEq(predicateSort, termSort) ? BoolToken.TRUE : BoolToken.FALSE;
        } else if (context.isSubsortedEq(predicateSort, termSort)) {
            return BoolToken.TRUE;
        } else if (null == context.getGLBSort(ImmutableSet.<String>of(predicateSort, termSort))) {
            return BoolToken.FALSE;
        } else {
            return kItem;
        }
    }

    public static Term isBuiltin(Term term, TermContext context) {
        // TODO(AndreiS): fix this predicate based on sorts
        if (term.kind().isComputational()) {
            term = KCollection.downKind(term);
        }

        if (term instanceof Token || term instanceof BuiltinList || term instanceof BuiltinSet
                || term instanceof BuiltinMap) {
            return BoolToken.TRUE;
        } else if (term.isGround()) {
            return BoolToken.FALSE;
        } else {
            throw new IllegalArgumentException("argument " + term + " is not ground");
        }
    }

    public static Term isToken(Term term, TermContext context) {
        // TODO(AndreiS): fix this predicate based on sorts
        if (term.kind().isComputational()) {
            term = KCollection.downKind(term);
        }

        if (term instanceof UninterpretedToken) {
            return BoolToken.TRUE;
        } else if (term.isGround()) {
            return BoolToken.FALSE;
        } else {
            throw new IllegalArgumentException("argument " + term + " is not ground");
        }
    }

}
