// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.kil.KList;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;


/**
 * TODO(YilongL): add documentation or remove this class
 *
 * @author AndreiS
 *
 */
public class KSubsortingToInjection extends CopyOnWriteTransformer {

    public KSubsortingToInjection(Context context) {
        super("Replace a KItem with a KSequence with one element", context);
    }

    @Override
    public TermCons visit(TermCons termCons, Void _void) {
        return termCons;
    }

    @Override
    public KList visit(KList kList, Void _void) {
        return kList;
    }

}
