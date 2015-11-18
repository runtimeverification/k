// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.builtin.KLabels;
import org.kframework.kore.*;

import static org.kframework.kore.KORE.*;

/**
 * Convert a term of any class implementing {@link org.kframework.kore.K}
 * to an equivalent term using the standard implementations
 * from {@link org.kframework.kore.KORE}.
 */
public class KtoKORE extends TransformKORE {
    @Override
    public K apply(KApply k) {
        if (k.klabel().name().equals(KLabels.KREWRITE)) {
            return KRewrite(apply(k.klist().items().get(0)), apply(k.klist().items().get(1)), k.att());
        } else {
            k = (KApply) super.apply(k);
            return KApply(apply(k.klabel()), k.klist(), k.att());
        }
    }

    private KLabel apply(KLabel klabel) {
        if (klabel instanceof KVariable)
            return apply((KVariable) klabel);
        return KLabel(klabel.name());
    }

    @Override
    public K apply(KRewrite k) {
        k = (KRewrite) super.apply(k);
        return KRewrite(k.left(), k.right(), k.att());
    }

    @Override
    public K apply(KToken k) {
        return KToken(k.s(), Sort(k.sort().name()), k.att());
    }

    @Override
    public KVariable apply(KVariable k) {
        return KVariable(k.name(), k.att());
    }

    @Override
    public K apply(KSequence k) {
        k = (KSequence) super.apply(k);
        return KSequence(k.items(), k.att());
    }

    @Override
    public K apply(InjectedKLabel k) {
        return InjectedKLabel(apply(k.klabel()), k.att());
    }
}
