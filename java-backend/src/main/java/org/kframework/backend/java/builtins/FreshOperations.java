// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;

import org.kframework.kore.KLabel;
import org.kframework.utils.errorsystem.KEMException;


/**
 * Implements generation of fresh constants.
 *
 * @author AndreiS
 */
public class FreshOperations {

    public static Term freshOfSort(Sort sort, TermContext context) {
        return fresh(StringToken.of(sort.toString()), context);
    }

    public static Term fresh(StringToken term, TermContext context) {
        KLabel name = context.definition().freshFunctionNames().get(Sort.parse(term.stringValue()));
        if (name == null) {
            throw KEMException.criticalError("Attempting to generate a fresh symbol of sort " + term.stringValue()
                    + " but no fresh function can be found.");
        }

        KItem freshFunction = KItem.of(
                KLabelConstant.of(name, context.definition()),
                KList.singleton(IntToken.of(context.freshConstant())),
                context.global());
        return freshFunction.resolveFunctionAndAnywhere(context);
    }

}
