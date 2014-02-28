package org.kframework.backend;

import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/17/12
 * Time: 6:24 PM
 */
public class BackendFilter extends BasicVisitor {
    protected StringBuilder result;

    public BackendFilter(Context context) {
        super(context);
        result = new java.lang.StringBuilder();
    }

    /**
     * @return The result as StringBuilder, rather than String, for performance considerations.
     */
    public StringBuilder getResult() {
        return result;
    }
}
