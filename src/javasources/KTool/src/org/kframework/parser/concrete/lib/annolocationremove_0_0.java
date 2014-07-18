// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.lib;

import org.spoofax.interpreter.terms.IStrategoList;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

/**
 * Example Java strategy implementation.
 *
 * This strategy can be used by editor services and can be called in Stratego modules by declaring it as an external strategy as follows:
 *
 * <code>
 *  external mergeamb(|)
 * </code>
 *
 * @see InteropRegisterer This class registers string_trim_last_one_0_0 for use.
 */
public class annolocationremove_0_0 extends Strategy {

    public static annolocationremove_0_0 instance = new annolocationremove_0_0();

    /**
     * Restructure a node from: [A(x1, x2 ... xn), A(y1, y2 ... yn), A ..., B] to : [A(amb([x1, y1, ...]), amb([x2, y2, ...]), ... amb([xn, yn, ...])), B]
     *
     * if the children of every A are located in the same places (see isSimilar(...)).
     */
    @Override
    public IStrategoTerm invoke(Context context, IStrategoTerm currentList) {
        context.push("annolocationremove_0_0");

        IStrategoList locList = context.getFactory().makeList();
        currentList = context.getFactory().annotateTerm(currentList, locList);
        context.popOnSuccess();
        return currentList;
    }
}
