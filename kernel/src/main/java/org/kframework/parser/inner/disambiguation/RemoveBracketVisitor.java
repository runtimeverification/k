// Copyright (c) K Team. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

import org.kframework.attributes.Att;
import org.kframework.parser.SafeTransformer;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;

public class RemoveBracketVisitor extends SafeTransformer {
    @Override
    public Term apply(TermCons tc) {
        if (tc.production().att().contains(Att.BRACKET()) ||
                tc.production().klabel().get().name().equals("#SyntacticCast") ||
                tc.production().klabel().get().name().equals("#InnerCast"))
        {
            return apply(tc.get(0));
        }
        return super.apply(tc);
    }
}
