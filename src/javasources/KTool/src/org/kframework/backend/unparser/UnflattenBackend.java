package org.kframework.backend.unparser;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.Backend;
import org.kframework.backend.BasicBackend;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.ConcretizeSyntax;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.IOException;

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
    public void run(Definition definition) throws IOException {
        /* first unflatten the syntax */
        ConcretizeSyntax concretizeSyntax = new ConcretizeSyntax(context);
        try {
            definition = (Definition)definition.accept(concretizeSyntax);
        } catch (TransformerException e) {
            System.err.println("Error unflattening syntax:");
            e.printStackTrace();
        }

        /* then unparse it */
        // TODO(YilongL): there should be an option to specify whether we want
        // to unparse it since two differently kompiled definition may look the
        // same after unparsing (e.g., empty list)
        UnparserFilter unparserFilter = new UnparserFilter(context);
        definition.accept(unparserFilter);

        String unparsedText = unparserFilter.getResult();

        FileUtil.save(context.dotk.getAbsolutePath() + "/def.k", unparsedText);

        FileUtil.save(options.directory.getPath() + File.separator + FilenameUtils.removeExtension(options.definition().getName()) + ".unparsed.k", unparsedText);
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