// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing;

import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.util.Utils;


/**
 * @author AndreiS
 */
public class FreezerIndex implements Index {

    private final KLabelConstant kLabel;
    private final int holeIndex;

    public FreezerIndex(KLabelConstant kLabel, int holeIndex) {
        this.kLabel = kLabel;
        this.holeIndex = holeIndex;
    }

    @Override
    public boolean isUnifiable(Index index) {
        if (index instanceof FreezerIndex) {
            FreezerIndex freezerIndex = (FreezerIndex) index;
            return kLabel.equals(freezerIndex.kLabel)
                   && (holeIndex == -1 || freezerIndex.holeIndex == -1
                       || holeIndex == freezerIndex.holeIndex);
        } else {
            return index instanceof TopIndex;
        }
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof FreezerIndex)) {
            return false;
        }

        FreezerIndex index = (FreezerIndex) object;
        return kLabel.equals(index.kLabel) && holeIndex == index.holeIndex;
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + kLabel.hashCode();
        hash = hash * Utils.HASH_PRIME + holeIndex;
        return hash;
    }

    @Override
    public String toString() {
        return "@" + kLabel + "[" + holeIndex + "]";
    }

}
