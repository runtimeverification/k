package org.kframework.backend.java.symbolic;

import org.kframework.kil.KList;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 4/27/13
 * Time: 7:39 PM
 * To change this template use File | Settings | File Templates.
 */
public class KSubsortingToInjection extends CopyOnWriteTransformer {

    public KSubsortingToInjection(Context context) {
        super("Replace a KItem with a KSequence with one element", context);
    }

    @Override
    public TermCons transform(TermCons termCons) {
        return termCons;
    }

    @Override
    public KList transform(KList kList) {
        return kList;
    }


}
