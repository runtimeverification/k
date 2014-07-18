// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.Backend;
import org.kframework.backend.BasicBackend;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.krun.ConcretizeSyntax;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;

import java.io.File;

public class UnflattenBackend extends BasicBackend {
    private Backend backend;

    public UnflattenBackend(Stopwatch sw, Context context, Backend backend) {
        super(sw, context);
        this.backend = backend;
    }

    @Override
    public Definition lastStep(Definition def) {
        return backend.lastStep(def);
    }

    @Override
    public Definition firstStep(Definition def) {
        return backend.firstStep(def);
    }

    @Override
    public void run(Definition definition) {
        /* first unflatten the syntax */
        ConcretizeSyntax concretizeSyntax = new ConcretizeSyntax(context);
        definition = (Definition) concretizeSyntax.visitNode(definition);

        /* then unparse it */
        // TODO(YilongL): there should be an option to specify whether we want
        // to unparse it since two differently kompiled definition may look the
        // same after unparsing (e.g., empty list)
        UnparserFilter unparserFilter = new UnparserFilter(context);
        unparserFilter.visitNode(definition);

        String unparsedText = unparserFilter.getResult();

        FileUtil.save(context.dotk.getAbsolutePath() + "/def.k", unparsedText);

        FileUtil.save(options.directory.getPath() + File.separator + FilenameUtils.removeExtension(options.mainDefinitionFile().getName()) + ".unparsed.k", unparsedText);
    }

    @Override
    public String getDefaultStep() {
        return backend.getDefaultStep();
    }

    @Override
    public boolean autoinclude() {
        return backend.autoinclude();
    }

    @Override
    public CompilerSteps<Definition> getCompilationSteps() {
        return backend.getCompilationSteps();
    }
}