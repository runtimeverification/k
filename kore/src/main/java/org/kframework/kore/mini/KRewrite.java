// Copyright (c) 2016-2019 K Team. All Rights Reserved.
package org.kframework.kore.mini;

import org.kframework.attributes.Att;
import org.kframework.kore.K;

/**
 * Created by dwightguth on 1/11/16.
 */
public class KRewrite extends org.kframework.kore.KRewrite_JavaWrapper {

    private K left, right;

    public KRewrite(K left, K right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public K left() {
        return left;
    }

    @Override
    public K right() {
        return right;
    }

    @Override
    public Att att() {
        return Att.empty();
    }
}
