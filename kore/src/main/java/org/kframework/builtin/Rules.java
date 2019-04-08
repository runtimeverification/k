// Copyright (c) 2019 K Team. All Rights Reserved.

package org.kframework.builtin;

import org.kframework.kore.K;
import org.kframework.kore.mini.KApply;
import org.kframework.kore.mini.KRewrite;
import org.kframework.kore.mini.KVariable;

public class Rules {
    public static final KRewrite STUCK_RULE = new KRewrite( KApply.of(KLabels.STRATEGY_CELL, KApply.of(KLabels.KSEQ, KApply.of(KLabels.DOTK),  new KVariable("_REST")))
                                                          , KApply.of(KLabels.STRATEGY_CELL, KApply.of(KLabels.KSEQ, KApply.of(KLabels.STUCK), new KVariable("_REST")))
                                                          );
}
