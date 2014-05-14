// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.lib;

import org.spoofax.interpreter.terms.IStrategoInt;
import org.spoofax.interpreter.terms.IStrategoList;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

import static org.strategoxt.lang.Term.NO_STRATEGIES;

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
public class annolocation_0_0 extends Strategy {

    public static annolocation_0_0 instance = new annolocation_0_0();

    /**
     * Restructure a node from: [A(x1, x2 ... xn), A(y1, y2 ... yn), A ..., B] to : [A(amb([x1, y1, ...]), amb([x2, y2, ...]), ... amb([xn, yn, ...])), B]
     * 
     * if the children of every A are located in the same places (see isSimilar(...)).
     */
    @Override
    public IStrategoTerm invoke(Context context, IStrategoTerm currentList) {
        context.push("annolocation_0_0");

        IStrategoTerm loc = context.invokePrimitive("SSL_EXT_origin_location", currentList, NO_STRATEGIES, new IStrategoTerm[] { currentList });
        IStrategoInt loc0 = context.getFactory().makeInt(0);
        IStrategoInt loc1 = context.getFactory().makeInt(0);
        IStrategoInt loc2 = context.getFactory().makeInt(0);
        IStrategoInt loc3 = context.getFactory().makeInt(0);

        if (loc != null && loc.getAllSubterms().length == 4) {
            loc0 = context.getFactory().makeInt(((IStrategoInt) loc.getSubterm(0)).intValue());
            loc1 = context.getFactory().makeInt(((IStrategoInt) loc.getSubterm(1)).intValue() + 1);
            loc2 = context.getFactory().makeInt(((IStrategoInt) loc.getSubterm(2)).intValue());
            loc3 = context.getFactory().makeInt(((IStrategoInt) loc.getSubterm(3)).intValue() + 2);
        }

        IStrategoList locList = context.getFactory().makeList(context.getFactory().makeTuple(loc0, loc1, loc2, loc3));
        currentList = context.getFactory().annotateTerm(currentList, locList);
        context.popOnSuccess();
        return currentList;
    }
}
