package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Sorted;
import org.kframework.backend.java.kil.Term;
import org.kframework.kil.loader.Context;

import com.google.common.collect.ImmutableSet;


/**
 * Utility class for checking sort membership predicates.
 * 
 * @author: AndreiS
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
        String sortName = ((KLabelConstant) kItem.kLabel()).label().substring("is".length());
        Sorted sorted = (Sorted) kItem.kList().getContents().get(0);

        if (kItem.kList().getContents().get(0) instanceof KItem
                && ((KItem) kItem.kList().getContents().get(0)).kLabel().isConstructor()) {
            return context.isSubsortedEq(sortName, sorted.sort()) ? BoolToken.TRUE : BoolToken.FALSE;
        } else if (context.isSubsortedEq(sortName, sorted.sort())) {
            return BoolToken.TRUE;
        } else if (null == context.getGLBSort(ImmutableSet.<String>of(sortName, sorted.sort()))) {
            return BoolToken.FALSE;
        } else {
            return kItem;
        }
    }

}
