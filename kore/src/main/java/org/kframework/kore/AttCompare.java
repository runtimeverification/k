// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore;

import org.kframework.attributes.Att;
import scala.collection.immutable.Map;

import java.util.Arrays;
import java.util.List;

import static scala.compat.java8.JFunction.*;

/**
 * Created by dwightguth on 6/17/15.
 */
public class AttCompare {
    private K k;
    private List<String> attNames;

    public AttCompare(K k, String... attNames) {
        this.k = k;
        this.attNames = Arrays.asList(attNames);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        AttCompare that = (AttCompare) o;

        return attEquals(this.k, that.k);

    }

    private boolean attEquals(K thisK, K thatK) {
        if (!filterAtt(thisK.att()).equals(filterAtt(thatK.att()))) {
            return false;
        }
        if ((thisK instanceof KToken && thatK instanceof KToken)
                || (thisK instanceof KVariable && thatK instanceof KVariable)
                || (thisK instanceof InjectedKLabel && thatK instanceof InjectedKLabel)) {
            return thisK.equals(thatK);
        } else if (thisK instanceof KApply && thatK instanceof KApply) {
            KApply thisKItem = (KApply) thisK;
            KApply thatKItem = (KApply) thatK;
            return thisKItem.klabel().equals(thatKItem.klabel()) && attEquals(thisKItem.klist().items(), thatKItem.klist().items());
        } else if (thisK instanceof KSequence && thatK instanceof KSequence) {
            return attEquals(((KSequence) thisK).items(), ((KSequence) thatK).items());
        } else if (thisK instanceof KRewrite && thatK instanceof KRewrite) {
            KRewrite thisKR = (KRewrite) thisK;
            KRewrite thatKR = (KRewrite) thatK;
            return attEquals(thisKR.left(), thatKR.left()) && attEquals(thisKR.right(), thatKR.right());
        } else {
            return false;
        }
    }

    private boolean attEquals(List<K> thisK, List<K> thatK) {
        if (thisK.size() != thatK.size()) {
            return false;
        }
        for (int i = 0; i < thisK.size(); i++) {
            if (!attEquals(thisK.get(i), thatK.get(i))) {
                return false;
            }
        }
        return true;
    }

    private Map<String, KApply> filterAtt(Att att) {
        return att.attMap().filterKeys(func(attNames::contains));
    }

    @Override
    public String toString() {
        return k.toString();
    }

    @Override
    public int hashCode() {
        return k.hashCode();
    }

    public K get() {
        return k;
    }
}
