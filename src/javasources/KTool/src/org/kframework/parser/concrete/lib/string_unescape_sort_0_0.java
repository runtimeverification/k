// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.lib;

import org.kframework.utils.StringUtil;
import org.spoofax.interpreter.terms.IStrategoString;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.spoofax.interpreter.terms.ITermFactory;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

/**
 * Example Java strategy implementation.
 * 
 * This strategy can be used by editor services and can be called in Stratego modules by declaring it as an external strategy as follows:
 * 
 * <code>
 *  external string-trim-last-one(|)
 * </code>
 * 
 * @see InteropRegisterer This class registers string_trim_last_one_0_0 for use.
 */
public class string_unescape_sort_0_0 extends Strategy {

    public static string_unescape_sort_0_0 instance = new string_unescape_sort_0_0();

    @Override
    public IStrategoTerm invoke(Context context, IStrategoTerm current) {
        IStrategoString istr = (IStrategoString) current;
        String str = istr.stringValue();

        str = StringUtil.unEscapeSortName(str);

        ITermFactory factory = context.getFactory();
        return factory.makeString(str);
    }
}
