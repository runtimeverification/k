// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/6/12
 * Time: 12:36 PM
 */
public abstract class BasicCompilerStep<T extends ASTNode> implements CompilerStep<T> {
    protected Stopwatch sw = null;
    protected Context context;

    public BasicCompilerStep(Context context) {
        this.context = context;
    }
    
    public void setSw(Stopwatch sw) {
        this.sw = sw;
    }
}
