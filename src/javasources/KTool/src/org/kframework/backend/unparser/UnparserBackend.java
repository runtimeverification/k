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

import java.io.File;

public class UnparserBackend extends BasicBackend {
    private boolean unflattenFirst; // unflatten syntax before unparsing

    @Inject
    UnparserBackend(Stopwatch sw, Context context) {
        super(sw, context);
        this.unflattenFirst = false;
    }

    public UnparserBackend(Stopwatch sw, Context context, boolean unflattenFirst) {
        super(sw, context);
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

        FileUtil.save(context.dotk.getAbsolutePath() + "/def.k", unparsedText);

        FileUtil.save(options.directory.getPath() + File.separator + FilenameUtils.removeExtension(options.mainDefinitionFile().getName()) + ".unparsed.k", unparsedText);
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
