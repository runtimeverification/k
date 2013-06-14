package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Sorted;
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

    public static BoolToken check(String sortName, Sorted sorted) {
        return context.isSubsortedEq(sortName, sorted.sort()) ? BoolToken.TRUE : BoolToken.FALSE;
    }

}
