// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend;

import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;

public abstract class PosterBackend {

    protected final Stopwatch sw;
    protected final Context context;

    public PosterBackend(Stopwatch sw, Context context) {
        this.sw = sw;
        this.context = context;
    }

    public abstract void run(Definition def);

}
