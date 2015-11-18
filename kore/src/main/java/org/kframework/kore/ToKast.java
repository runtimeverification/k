// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore;

/**
 * Created by dwightguth on 11/16/15.
 */
@Deprecated
public class ToKast {

    public static String apply(K k) {
        return org.kframework.unparser.ToKast.apply(k);
    }

    public static String apply(KLabel l) {
        return org.kframework.unparser.ToKast.apply(l);
    }
}
