// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;

import com.google.common.collect.Lists;


/**
 * Implements generation of fresh constants.
 *
 * @author AndreiS
 */
public class FreshOperations {

    private FreshOperations() { }

    public static Term fresh(Sort sort, TermContext context) {
        return fresh(StringToken.of(sort.name()), context);
    }

    public static Term fresh(StringToken term, TermContext context) {
        String name = context.definition().context().freshFunctionNames.get(term.stringValue());
        if (name == null) {
            throw new UnsupportedOperationException();
        }

        KItem freshFunction = KItem.of(
                KLabelConstant.of(name, context.definition()),
                new KList(Lists.newArrayList((Term) IntToken.of(context.incrementCounter()))),
                context);
        return freshFunction.evaluateFunction(false, context);
    }

}
