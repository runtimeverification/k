// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.latex;

import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;

import com.google.inject.Inject;

public class DocumentationBackend extends LatexBackend {

    @Inject
    DocumentationBackend(Stopwatch sw, Context context) {
        super(sw, context, true);
    }
}
