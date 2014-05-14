// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.lib;

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
public class xml_string_escape_from_string_0_0 extends Strategy {

    public static xml_string_escape_from_string_0_0 instance = new xml_string_escape_from_string_0_0();

    @Override
    public IStrategoTerm invoke(Context context, IStrategoTerm current) {
        IStrategoString istr = (IStrategoString) current;
        String str = istr.stringValue();

        StringBuilder sb = new StringBuilder();
        for (int i = 1; i < str.length() - 1; i++) {
            if (str.charAt(i) == '&')
                sb.append("&amp;");
            else if (str.charAt(i) == '>')
                sb.append("&gt;");
            else if (str.charAt(i) == '<')
                sb.append("&lt;");
            else if (str.charAt(i) == '\\' && str.charAt(i + 1) == '\"') {
                sb.append("&quot;");
                i++;
            } else if (str.charAt(i) == '\\' && str.charAt(i + 1) == '\\') {
                sb.append("\\");
                i++;
            } else
                sb.append(str.charAt(i));
        }

        ITermFactory factory = context.getFactory();
        return factory.makeString(sb.toString());
    }
}
