// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.krun.ConcretizeSyntax;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;

import com.google.inject.Inject;

public class UnparserBackend extends BasicBackend {
    private boolean unflattenFirst; // unflatten syntax before unparsing

    private final FileUtil files;

    @Inject
    UnparserBackend(Stopwatch sw, Context context, FileUtil files) {
        super(sw, context);
        this.unflattenFirst = false;
        this.files = files;
    }

    public UnparserBackend(Stopwatch sw, Context context, boolean unflattenFirst, FileUtil files) {
        super(sw, context);
        this.unflattenFirst = unflattenFirst;
        this.files = files;
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

    @Override
    public String getDefaultStep() {
        return "FirstStep";
    }

    @Override
    public boolean documentation() {
        return false;
    }

    @Override
    public boolean generatesDefinition() {
        return false;
    }

}
