// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.PosterBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.ConcretizeSyntax;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;

import com.google.inject.Inject;

public class UnparserBackend extends PosterBackend {
    private boolean unflattenFirst; // unflatten syntax before unparsing

    private final FileUtil files;
    private final KompileOptions options;

    @Inject
    UnparserBackend(Stopwatch sw, Context context, KompileOptions options, FileUtil files) {
        super(sw, context);
        this.unflattenFirst = false;
        this.files = files;
        this.options = options;
    }

    public UnparserBackend(Stopwatch sw, Context context, KompileOptions options, boolean unflattenFirst, FileUtil files) {
        this(sw, context, options, files);
        this.unflattenFirst = unflattenFirst;
    }

    @Override
    public void run(Definition definition) {
        if (unflattenFirst) {
            ConcretizeSyntax concretizeSyntax = new ConcretizeSyntax(context);
            definition = (Definition) concretizeSyntax.visitNode(definition);
        }
        UnparserFilter unparserFilter = new UnparserFilter(context);
        unparserFilter.visitNode(definition);

        String unparsedText = unparserFilter.getResult();

        files.saveToDefinitionDirectory(FilenameUtils.removeExtension(options.mainDefinitionFile().getName()) + ".unparsed.k", unparsedText);
    }

}
