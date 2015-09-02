// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.builtin;

import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KToken;

import static org.kframework.kore.KORE.KApply;
import static org.kframework.kore.KORE.KLabel;
import static org.kframework.kore.KORE.KToken;
import static org.kframework.kore.KORE.Sort;

/**
 * Created by dwightguth on 4/17/15.
 */
public class BooleanUtils {

    public static KApply and(K k1, K k2) {
        return KApply(KLabel("_andBool_"), k1, k2);
    }
    public static KApply not(K k) { return KApply(KLabel("notBool_"), k); }

    public static final KToken TRUE = KToken("true", Sort("Bool"));
    public static final KToken FALSE = KToken("false", Sort("Bool"));
}
