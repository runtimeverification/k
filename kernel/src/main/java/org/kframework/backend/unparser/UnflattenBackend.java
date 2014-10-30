// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;

import com.google.inject.Inject;

public class UnflattenBackend extends UnparserBackend {

    @Inject
    UnflattenBackend(Stopwatch sw, Context context, FileUtil files) {
        super(sw, context, true, files);
    }
}