// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing;

import org.kframework.backend.java.kil.KLabelConstant;


/**
 * @author: AndreiS
 */
public class KLabelIndex implements Index {

    private final KLabelConstant kLabel;

    public KLabelIndex(KLabelConstant kLabel) {
        this.kLabel = kLabel;
    }

    public KLabelConstant kLabel() {
        return kLabel;
    }

    @Override
    public boolean isUnifiable(Index index) {
        return index instanceof TopIndex || equals(index);
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof KLabelIndex)) {
            return false;
        }

        KLabelIndex index = (KLabelIndex) object;
        return kLabel.equals(index.kLabel);
    }

    @Override
    public int hashCode() {
        return kLabel.hashCode();
    }

    @Override
    public String toString() {
        return "@" + kLabel;
    }

}
