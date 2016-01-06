// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;

import org.kframework.utils.errorsystem.KEMException;


/**
 * Implements generation of fresh constants.
 *
 * @author AndreiS
 */
public class FreshOperations {

    public static Term freshOfSort(Sort sort, TermContext context) {
        return fresh(StringToken.of(sort.name()), context);
    }

    public static Term fresh(StringToken term, TermContext context) {
        String name = context.definition().freshFunctionNames().get(Sort.of(term.stringValue()));
        if (name == null) {
            throw KEMException.criticalError("Attempting to generate a fresh symbol of sort " + term.stringValue()
                    + " but no fresh function can be found.");
        }

        KItem freshFunction = KItem.of(
                KLabelConstant.of(name, context.definition()),
                KList.singleton(IntToken.of(context.freshConstant())),
                context.global());
        return freshFunction.evaluateFunction(false, context);
    }

}
