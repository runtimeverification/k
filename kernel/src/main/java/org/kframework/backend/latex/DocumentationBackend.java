// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.latex;

import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;

import com.google.inject.Inject;

public class DocumentationBackend extends LatexBackend {

    @Inject
    DocumentationBackend(Stopwatch sw, Context context, KompileOptions options, FileUtil files) {
        super(sw, context, options, true, files);
    }
}
