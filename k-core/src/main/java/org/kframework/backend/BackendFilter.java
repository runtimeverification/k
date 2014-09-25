// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend;

import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.NonCachingVisitor;
import org.kframework.kompile.KompileOptions;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/17/12
 * Time: 6:24 PM
 */
public class BackendFilter extends NonCachingVisitor {
    protected StringBuilder result;
    protected KompileOptions options;

    public BackendFilter(Context context) {
        super(context);
        this.options = context.kompileOptions;
        result = new java.lang.StringBuilder();
    }

    /**
     * @return The result as StringBuilder, rather than String, for performance considerations.
     */
    public StringBuilder getResult() {
        return result;
    }
}
