// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete.lib;

import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

/**
 * Example Java strategy implementation.
 *
 * This strategy can be used by editor services and can be called in Stratego
 * modules by declaring it as an external strategy as follows:
 *
 * <code>
 *  external string-trim-last-one(|)
 * </code>
 *
 * @see InteropRegisterer This class registers string_trim_last_one_0_0 for use.
 */
public class clear_console_0_0 extends Strategy {

    public static clear_console_0_0 instance = new clear_console_0_0();

    public final static String conName = "Spoofax Console";

    @Override
    public IStrategoTerm invoke(Context context, IStrategoTerm current) {
        return current;
    }

}