package org.kframework.backend.java.builtins;

import com.google.common.collect.ImmutableSet;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Sorted;
import org.kframework.backend.java.kil.Term;
import org.kframework.kil.loader.Context;


/**
 * @author: AndreiS
 */
public class SortMembership {

    private static Context context = null;

    public static void init(Context context) {
        assert SortMembership.context == null;

        SortMembership.context = context;
    }

    public static Term check(KItem kItem) {
        String sortName = ((KLabelConstant) kItem.kLabel()).label().substring("is".length());
        Sorted sorted = (Sorted) kItem.kList().getItems().get(0);

        if (kItem.kList().getItems().get(0) instanceof KItem
                && ((KItem) kItem.kList().getItems().get(0)).kLabel().isConstructor()) {
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
