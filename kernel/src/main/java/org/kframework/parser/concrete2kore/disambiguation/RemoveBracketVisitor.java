// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import org.kframework.parser.SafeTransformer;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;

public class RemoveBracketVisitor extends SafeTransformer {
    @Override
    public Term apply(TermCons tc) {
        if (tc.production().att().contains("bracket") ||
                tc.production().klabel().get().name().equals("#SyntacticCast") ||
                tc.production().klabel().get().name().equals("#InnerCast") ||
                tc.production().klabel().get().name().equals("#OuterCast"))
        {
            return apply(tc.get(0));
        }
        return super.apply(tc);
    }
}
